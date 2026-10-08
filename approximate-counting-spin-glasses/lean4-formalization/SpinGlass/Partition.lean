import SpinGlass.Expansion
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Ising partition function and graphical normalization

`x e` is the real interaction coefficient, including β and the N scaling.
These identities hold for every finite array, so no moment or symmetry
assumptions are hidden in this finite part of the argument.
-/

namespace SpinGlass.Partition

noncomputable section
open scoped BigOperators
open SpinGlass.Expansion

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- Partition function over the full finite Ising cube. -/
def partitionFunction (incidence : E → Finset V) (edges : Finset E) (x : E → ℝ) : ℝ :=
  ∑ σ : V → Bool, Real.exp (∑ e ∈ edges, x e * edgeCharacter incidence σ e)

/-- Explicit product prefactor used in the paper. -/
def prefactor (edges : Finset E) (x : E → ℝ) : ℝ :=
  (2 : ℝ) ^ Fintype.card V * ∏ e ∈ edges, Real.cosh (x e)

/-- Normalized partition function. -/
def normalizedPartition (incidence : E → Finset V) (edges : Finset E) (x : E → ℝ) : ℝ :=
  partitionFunction incidence edges x / prefactor (V := V) edges x

theorem exp_spin_factor {s : ℝ} (hs : |s| = 1) (x : ℝ) :
    Real.exp (x * s) = Real.cosh x * (1 + Real.tanh x * s) := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hs with h | h
  · rw [h, mul_one, mul_one, Real.tanh_eq_sinh_div_cosh]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hc, Real.cosh_add_sinh]
  · rw [h, mul_neg_one, mul_neg_one, Real.tanh_eq_sinh_div_cosh]
    have he := Real.cosh_sub_sinh x
    field_simp
    nlinarith

omit [DecidableEq V] in
theorem prefactor_pos (edges : Finset E) (x : E → ℝ) :
    0 < prefactor (V := V) edges x := by
  apply mul_pos (pow_pos (by norm_num) _)
  exact Finset.prod_pos (fun e _ => Real.cosh_pos (x e))

theorem partition_pos (incidence : E → Finset V) (edges : Finset E) (x : E → ℝ) :
    0 < partitionFunction incidence edges x := by
  apply Finset.sum_pos
  · intro σ _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- Full finite graphical identity, starting with the exponential partition function. -/
theorem partition_eq_prefactor_mul_even_sum
    (incidence : E → Finset V) (edges : Finset E) (x : E → ℝ) :
    partitionFunction incidence edges x = prefactor (V := V) edges x *
      ∑ Γ ∈ edges.powerset.filter (IsEven incidence), ∏ e ∈ Γ, Real.tanh (x e) := by
  unfold partitionFunction
  simp_rw [Real.exp_sum]
  have hf : ∀ σ : V → Bool,
      (∏ e ∈ edges, Real.exp (x e * edgeCharacter incidence σ e)) =
        (∏ e ∈ edges, Real.cosh (x e)) *
          ∏ e ∈ edges, (1 + Real.tanh (x e) * edgeCharacter incidence σ e) := by
    intro σ
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    exact exp_spin_factor (abs_edgeCharacter incidence σ e) (x e)
  simp_rw [hf]
  rw [← Finset.mul_sum, graphical_expansion_sum]
  unfold prefactor
  ring

/-- The normalized partition function is exactly the even-hypergraph polynomial. -/
theorem normalizedPartition_eq_even_sum
    (incidence : E → Finset V) (edges : Finset E) (x : E → ℝ) :
    normalizedPartition incidence edges x =
      ∑ Γ ∈ edges.powerset.filter (IsEven incidence), ∏ e ∈ Γ, Real.tanh (x e) := by
  unfold normalizedPartition
  rw [partition_eq_prefactor_mul_even_sum]
  exact mul_div_cancel_left₀ _ (ne_of_gt (prefactor_pos edges x))

theorem normalizedPartition_pos
    (incidence : E → Finset V) (edges : Finset E) (x : E → ℝ) :
    0 < normalizedPartition incidence edges x :=
  div_pos (partition_pos incidence edges x) (prefactor_pos edges x)


/-- The target log partition function splits exactly into the prefactor and correction. -/
theorem log_partition_decomposition
    (incidence : E → Finset V) (edges : Finset E) (x : E → ℝ) :
    Real.log (partitionFunction incidence edges x) =
      Real.log (prefactor (V := V) edges x) +
        Real.log (normalizedPartition incidence edges x) := by
  rw [normalizedPartition, Real.log_div
    (ne_of_gt (partition_pos incidence edges x)) (ne_of_gt (prefactor_pos edges x))]
  ring

end
end SpinGlass.Partition

