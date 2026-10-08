import SpinGlass.Expansion
import Mathlib.Analysis.Complex.Exponential

/-!
# Exact finite graphical mass and exponential comparison

The graphical mass is an actual finite sum over the even edge subsets. Its
spin-average representation follows from the proved parity expansion. Sign
orthogonality identifies the squared graphical weights with the same average
at squared edge amplitudes. The elementary exponential comparison requires
absolute coefficients at most one, so every product factor is nonnegative.

No uniform-in-dimension entropy estimate, temperature threshold, or graphical
mass constant is assumed or proved here.
-/

noncomputable section

namespace SpinGlass.GraphicalMass

open Finset
open SpinGlass.Expansion

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- The weighted mass of the actual even subsets of a finite edge family. -/
def graphicalMass (incidence : E → Finset V) (edges : Finset E) (a : E → ℝ) : ℝ :=
  ∑ Γ ∈ edges.powerset.filter (IsEven incidence), ∏ e ∈ Γ, a e

/-- Exact mass identity for arbitrary real edge coefficients. The averaging
coordinates can be viewed as independent uniform overlap signs. -/
theorem graphicalMass_eq_spinMean (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) :
    graphicalMass incidence edges a =
      spinMean (fun σ : V → Bool =>
        ∏ e ∈ edges, (1 + a e * edgeCharacter incidence σ e)) :=
  (graphical_expansion incidence edges a).symm

/-- The sum of squared graph weights is the overlap-spin average at squared
edge amplitudes. No size restriction on the amplitudes is needed for this identity. -/
theorem squared_graph_weights_eq_spinMean (incidence : E → Finset V)
    (edges : Finset E) (a : E → ℝ) :
    (∑ Γ ∈ edges.powerset.filter (IsEven incidence), (∏ e ∈ Γ, a e) ^ 2) =
      spinMean (fun σ : V → Bool =>
        ∏ e ∈ edges, (1 + (a e) ^ 2 * edgeCharacter incidence σ e)) := by
  rw [graphical_expansion]
  simp only [Finset.prod_pow]

/-- Averaging the square of the signed graphical polynomial over independent
edge signs equals the overlap-spin product at squared edge amplitudes. -/
theorem sign_second_moment_eq_spinMean [Fintype E] [DecidableEq E]
    (incidence : E → Finset V) (edges : Finset E) (a : E → ℝ) :
    spinMean (fun η : E → Bool =>
      (∑ Γ ∈ edges.powerset.filter (IsEven incidence),
        ∏ e ∈ Γ, (a e * spinSign (η e))) ^ 2) =
      spinMean (fun σ : V → Bool =>
        ∏ e ∈ edges, (1 + (a e) ^ 2 * edgeCharacter incidence σ e)) := by
  rw [edge_subset_second_moment, graphical_expansion]

omit [Fintype V] [DecidableEq V] in
/-- The product factors are nonnegative when absolute edge coefficients are
at most one, making the pointwise exponential comparison legitimate. -/
theorem spin_product_le_exp_sum (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) (ha : ∀ e ∈ edges, |a e| ≤ 1) (σ : V → Bool) :
    (∏ e ∈ edges, (1 + a e * edgeCharacter incidence σ e)) ≤
      Real.exp (∑ e ∈ edges, a e * edgeCharacter incidence σ e) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro e he
    have habs : |a e * edgeCharacter incidence σ e| ≤ 1 := by
      simpa only [abs_mul, abs_edgeCharacter, mul_one] using ha e he
    have hlo := (abs_le.mp habs).1
    linarith
  · intro e he
    simpa only [add_comm] using Real.add_one_le_exp (a e * edgeCharacter incidence σ e)

/-- The finite graphical mass is bounded by the explicit exponential moment.
The condition on absolute coefficients is essential for the product comparison. -/
theorem graphicalMass_le_exp_moment (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) (ha : ∀ e ∈ edges, |a e| ≤ 1) :
    graphicalMass incidence edges a ≤
      spinMean (fun σ : V → Bool =>
        Real.exp (∑ e ∈ edges, a e * edgeCharacter incidence σ e)) := by
  rw [graphicalMass_eq_spinMean]
  unfold spinMean
  apply mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun σ _ => spin_product_le_exp_sum incidence edges a ha σ))
  exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)

/-- The constant-weight finite step used by the paper's graphical mass argument.
The resulting exponential moment still needs the separate uniform entropy bound. -/
theorem uniform_mass_le_exp_moment (incidence : E → Finset V) (edges : Finset E)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑ Γ ∈ edges.powerset.filter (IsEven incidence), z ^ Γ.card) ≤
      spinMean (fun σ : V → Bool =>
        Real.exp (z * ∑ e ∈ edges, edgeCharacter incidence σ e)) := by
  have h := graphicalMass_le_exp_moment incidence edges (fun _ => z)
    (fun _ _ => by simpa only [abs_of_nonneg hz] using hz1)
  simpa only [graphicalMass, Finset.prod_const, ← Finset.mul_sum] using h

/-- Specialization to the actual distinct-index pure p-spin interaction family. -/
theorem pure_p_spin_mass_le_exp_moment (N p : ℕ) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑ Γ ∈ ((Finset.univ : Finset (Fin N)).powersetCard p).powerset.filter
        (IsEven id), z ^ Γ.card) ≤
      spinMean (fun σ : Fin N → Bool =>
        Real.exp (z * ∑ e ∈ (Finset.univ : Finset (Fin N)).powersetCard p,
          edgeCharacter id σ e)) :=
  uniform_mass_le_exp_moment id _ hz hz1

end SpinGlass.GraphicalMass
