import SpinGlass.ArithmeticEvaluation
import SpinGlass.SupportMeanSquare
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact higher-order support evaluation and arithmetic cost

The evaluator uses the explicitly counted local spin loops, followed by the
alternating support transform and a sum over the retained vertex supports.
-/

noncomputable section
namespace SpinGlass.SupportEvaluation
open Finset
open SpinGlass.ArithmeticEvaluation SpinGlass.Expansion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One Möbius transform, actually evaluated by a finite subset loop. -/
def supportEvaluator (edges : Finset (Finset V)) (weight : Finset V → ℝ)
    (U : Finset V) : Computation :=
  sumFinset U.powerset (fun S =>
    mul (literal ((-1 : ℝ)^(U.card-S.card))) (localEvaluator edges weight S))

/-- Algorithm 1's support loop, with every local sum evaluated independently. -/
def higherEvaluator (p cutoff : ℕ) (weight : Finset V → ℝ) : Computation :=
  sumFinset (Finset.range (cutoff+1)) (fun v =>
    sumFinset ((Finset.univ : Finset V).powersetCard v)
      (supportEvaluator ((Finset.univ : Finset V).powersetCard p) weight))

/-- The evaluated transform agrees with the exact support identity. -/
theorem supportEvaluator_value (edges : Finset (Finset V)) (weight : Finset V → ℝ)
    (U : Finset V) :
    (supportEvaluator edges weight U).value =
      ∑ Γ ∈ edges.powerset.filter (IsEven id) with SpinGlass.Hypergraph.support Γ = U,
        ∏ e ∈ Γ, weight e := by
  have h := SpinGlass.Mobius.transform_Gspin_eq_exact_support edges weight U
  rw [← h]
  simp only [supportEvaluator, sumFinset_value, mul, literal, localEvaluator_value,
    SpinGlass.Mobius.transform, SpinGlass.LocalCube.Gspin_eq_localGspin]

/-- The full evaluator returns exactly the retained signed graph polynomial. -/
theorem higherEvaluator_value (p cutoff : ℕ) (weight : Finset V → ℝ) :
    (higherEvaluator p cutoff weight).value =
      ∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs p : Finset (Finset (Finset V))).filter
        (fun Γ => (SpinGlass.Hypergraph.support Γ).card ≤ cutoff), ∏ e ∈ Γ, weight e := by
  simp only [higherEvaluator, sumFinset_value, supportEvaluator_value]
  have hinner : ∀ v, (∑ U ∈ (Finset.univ : Finset V).powersetCard v,
      ∑ Γ ∈ ((Finset.univ : Finset V).powersetCard p).powerset.filter (IsEven id) with
        SpinGlass.Hypergraph.support Γ = U, ∏ e ∈ Γ, weight e) =
      ∑ Γ ∈ ((Finset.univ : Finset V).powersetCard p).powerset.filter (IsEven id) with
        (SpinGlass.Hypergraph.support Γ).card = v, ∏ e ∈ Γ, weight e := by
    intro v
    rw [Finset.sum_fiberwise_eq_sum_filter]
    congr 1
    ext Γ
    simp
  simp_rw [hinner]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  ext Γ
  simp [SpinGlass.SupportMassCounting.evenGraphs, Nat.lt_succ_iff]

/-- Agreement with the actual disorder-dependent approximation in the MSE theorem. -/
theorem higherEvaluator_disorder_value (p cutoff : ℕ) (a : ℝ) (J : Finset V → ℝ) :
    (higherEvaluator p cutoff (fun e => SpinGlass.Disorder.weight a (J e))).value =
      SpinGlass.SupportMeanSquare.supportApproximation p cutoff a J := by
  rw [higherEvaluator_value]
  rfl

/-- The exact arithmetic-operation count of one Möbius transform. -/
theorem supportEvaluator_operations (edges : Finset (Finset V)) (weight : Finset V → ℝ)
    (U : Finset V) :
    (supportEvaluator edges weight U).operations =
      ∑ S ∈ U.powerset, ((localEvaluator edges weight S).operations + 2) := by
  simp [supportEvaluator, sumFinset_operations, mul, literal,
    Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  ring

/-- A local incidence is a subset of the corresponding ambient edge. -/
theorem localIncidence_card_le (S e : Finset V) :
    (SpinGlass.LocalCube.localIncidence S e).card ≤ e.card := by
  rw [SpinGlass.LocalCube.localIncidence, Finset.card_subtype]
  exact Finset.card_filter_le _ _

/-- Exact loop counts yield a uniform local-cube operation bound. -/
theorem localEvaluator_cost {p : ℕ} (hp : 0 < p) (weight : Finset V → ℝ) (S : Finset V) :
    (localEvaluator ((Finset.univ : Finset V).powersetCard p) weight S).operations ≤
      (p+6) * (Fintype.card V + 1)^p * 2^S.card := by
  let N := Fintype.card V
  let M := (((Finset.univ : Finset V).powersetCard p).filter (fun e => e ⊆ S)).card
  let P := (N+1)^p
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hNP : N ≤ P := by
    calc
      N ≤ N+1 := by omega
      _ ≤ (N+1)^p := Nat.le_self_pow hp.ne' (N+1)
  have hSP : S.card ≤ P := (Finset.card_le_univ S).trans hNP
  have hMP : M ≤ P := by
    calc
      M ≤ ((Finset.univ : Finset V).powersetCard p).card := Finset.card_filter_le _ _
      _ = N.choose p := by simp [N]
      _ ≤ N^p := Nat.choose_le_pow _ _
      _ ≤ (N+1)^p := Nat.pow_le_pow_left (by omega) _
  have hsum : (∑ e ∈ ((Finset.univ : Finset V).powersetCard p).filter (fun e => e ⊆ S),
      (SpinGlass.LocalCube.localIncidence S e).card) ≤ M*p := by
    calc
      _ ≤ ∑ _e ∈ ((Finset.univ : Finset V).powersetCard p).filter (fun e => e ⊆ S), p := by
        apply Finset.sum_le_sum
        intro e he
        have hep := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
        exact (localIncidence_card_le S e).trans hep.le
      _ = M*p := by simp [M]
  have h2 : 1 ≤ 2^S.card := Nat.one_le_pow _ _ (by norm_num)
  rw [localEvaluator_operations]
  change S.card + 2^S.card *
    ((∑ e ∈ ((Finset.univ : Finset V).powersetCard p).filter (fun e => e ⊆ S),
      (SpinGlass.LocalCube.localIncidence S e).card) + 3*M+1) + 1 ≤ (p+6)*P*2^S.card
  have hinside : (∑ e ∈ ((Finset.univ : Finset V).powersetCard p).filter (fun e => e ⊆ S),
      (SpinGlass.LocalCube.localIncidence S e).card) + 3*M+1 ≤ (p+4)*P := by nlinarith
  have hscale := Nat.mul_le_mul_left (2^S.card) hinside
  have hpows := Nat.mul_le_mul_left P h2
  nlinarith

/-- Summing over the actual subsets gives exactly `3^|U|`. -/
theorem sum_cube_sizes (U : Finset V) : (∑ S ∈ U.powerset, (2:ℕ)^S.card) = 3^U.card := by
  have h := Finset.sum_pow_mul_eq_add_pow (2:ℕ) 1 U
  simpa using h

/-- The Möbius evaluator is exponential only in the selected support size. -/
theorem supportEvaluator_cost {p : ℕ} (hp : 0 < p) (weight : Finset V → ℝ) (U : Finset V) :
    (supportEvaluator ((Finset.univ : Finset V).powersetCard p) weight U).operations ≤
      (p+8) * (Fintype.card V+1)^p * 3^U.card := by
  rw [supportEvaluator_operations]
  calc
    _ ≤ ∑ S ∈ U.powerset, (p+8) * (Fintype.card V+1)^p * 2^S.card := by
      apply Finset.sum_le_sum
      intro S hS
      have h := localEvaluator_cost hp weight S
      have hP : 1 ≤ (Fintype.card V+1)^p := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ 2^S.card := Nat.one_le_pow _ _ (by norm_num)
      nlinarith
    _ = _ := by rw [← Finset.mul_sum, sum_cube_sizes]

/-- The actual retained-support enumeration has the stated binomial weight. -/
theorem support_enumeration_weight (cutoff : ℕ) (hcut : cutoff ≤ Fintype.card V) :
    (∑ U ∈ (Finset.univ : Finset V).powerset.filter (fun U => U.card ≤ cutoff), (3:ℕ)^U.card) =
      ∑ v ∈ Finset.range (cutoff+1), (Fintype.card V).choose v * 3^v := by
  rw [Finset.sum_filter, Finset.sum_powerset]
  have hinner : ∀ j, (∑ U ∈ (Finset.univ : Finset V).powersetCard j,
      if U.card ≤ cutoff then (3:ℕ)^U.card else 0) =
      if j ≤ cutoff then (Fintype.card V).choose j * 3^j else 0 := by
    intro j
    rw [Finset.sum_powersetCard j (Finset.univ : Finset V)
      (fun n => if n ≤ cutoff then (3:ℕ)^n else 0)]
    split_ifs <;> simp [nsmul_eq_mul]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.card_univ]
  omega

/-- Proposition 5.1's operation bound, derived from the actual nested bounded
support generator. The outer cardinality loop is counted as well. -/
theorem higherEvaluator_cost {p cutoff : ℕ} (hp : 0 < p)
    (hcut : cutoff ≤ Fintype.card V) (weight : Finset V → ℝ) :
    (higherEvaluator p cutoff weight).operations ≤
      (p+10) * (Fintype.card V+1)^p *
        ∑ v ∈ Finset.range (cutoff+1), (Fintype.card V).choose v * 3^v := by
  have hP : 1 ≤ (Fintype.card V+1)^p := Nat.one_le_pow _ _ (by omega)
  have hinner : ∀ v, (sumFinset ((Finset.univ : Finset V).powersetCard v)
      (supportEvaluator ((Finset.univ : Finset V).powersetCard p) weight)).operations ≤
      (p+9) * (Fintype.card V+1)^p * (Fintype.card V).choose v * 3^v := by
    intro v
    rw [sumFinset_operations]
    have heq : (∑ U ∈ (Finset.univ : Finset V).powersetCard v,
        (supportEvaluator ((Finset.univ : Finset V).powersetCard p) weight U).operations) +
        ((Finset.univ : Finset V).powersetCard v).card =
        ∑ U ∈ (Finset.univ : Finset V).powersetCard v,
          ((supportEvaluator ((Finset.univ : Finset V).powersetCard p) weight U).operations+1) := by
      simp [Finset.sum_add_distrib]
    rw [heq]
    calc
      _ ≤ ∑ U ∈ (Finset.univ : Finset V).powersetCard v,
          (p+9) * (Fintype.card V+1)^p * 3^v := by
        apply Finset.sum_le_sum
        intro U hU
        have h := supportEvaluator_cost hp weight U
        rw [(Finset.mem_powersetCard.mp hU).2] at h
        have h3 : 1 ≤ 3^v := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      _ = _ := by simp [Finset.card_powersetCard]; ring
  rw [higherEvaluator, sumFinset_operations]
  have heq : (∑ v ∈ Finset.range (cutoff+1),
      (sumFinset ((Finset.univ : Finset V).powersetCard v)
        (supportEvaluator ((Finset.univ : Finset V).powersetCard p) weight)).operations) +
      (Finset.range (cutoff+1)).card =
      ∑ v ∈ Finset.range (cutoff+1),
        ((sumFinset ((Finset.univ : Finset V).powersetCard v)
          (supportEvaluator ((Finset.univ : Finset V).powersetCard p) weight)).operations+1) := by
    simp [Finset.sum_add_distrib]
  rw [heq]
  calc
    _ ≤ ∑ v ∈ Finset.range (cutoff+1),
        (p+10) * (Fintype.card V+1)^p * ((Fintype.card V).choose v * 3^v) := by
      apply Finset.sum_le_sum
      intro v hv
      have h := hinner v
      have hvN : v ≤ Fintype.card V := by have := Finset.mem_range.mp hv; omega
      have hc : 1 ≤ (Fintype.card V).choose v := Nat.choose_pos hvN
      have h3 : 1 ≤ 3^v := Nat.one_le_pow _ _ (by norm_num)
      have hprod : 1 ≤ (Fintype.card V+1)^p * ((Fintype.card V).choose v * 3^v) := by
        simpa using Nat.mul_le_mul hP (Nat.mul_le_mul hc h3)
      nlinarith
    _ = _ := by rw [Finset.mul_sum]

/-- The actual number of iterations of the two outer bounded-support loops. -/
def supportIndexVisits (cutoff : ℕ) : ℕ :=
  (Finset.range (cutoff+1)).card +
    ∑ v ∈ Finset.range (cutoff+1), ((Finset.univ : Finset V).powersetCard v).card

/-- The generator itself visits only the bounded-cardinality supports; it does
not enumerate the ambient powerset and reject almost all of it. -/
theorem supportIndexVisits_bound (cutoff : ℕ) (hcut : cutoff ≤ Fintype.card V) :
    supportIndexVisits (V := V) cutoff ≤
      2 * ∑ v ∈ Finset.range (cutoff+1), (Fintype.card V).choose v * 3^v := by
  unfold supportIndexVisits
  have h1 : (Finset.range (cutoff+1)).card ≤
      ∑ v ∈ Finset.range (cutoff+1), (Fintype.card V).choose v * 3^v := by
    have heq : (∑ _v ∈ Finset.range (cutoff+1), (1:ℕ)) = (Finset.range (cutoff+1)).card := by simp
    rw [← heq]
    apply Finset.sum_le_sum
    intro v hv
    have hvN : v ≤ Fintype.card V := by have := Finset.mem_range.mp hv; omega
    have hc : 1 ≤ (Fintype.card V).choose v := Nat.choose_pos hvN
    have h3 : 1 ≤ 3^v := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  have h2 : (∑ v ∈ Finset.range (cutoff+1), ((Finset.univ : Finset V).powersetCard v).card) ≤
      ∑ v ∈ Finset.range (cutoff+1), (Fintype.card V).choose v * 3^v := by
    apply Finset.sum_le_sum
    intro v hv
    simp only [Finset.card_powersetCard, Finset.card_univ]
    have h3 : 1 ≤ 3^v := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  omega

/-- The exact branch evaluates one ambient spin cube. -/
def exactEvaluator (p : ℕ) (weight : Finset V → ℝ) : Computation :=
  localEvaluator ((Finset.univ : Finset V).powersetCard p) weight Finset.univ

/-- The exact branch returns the actual normalized partition function. -/
theorem exactEvaluator_disorder_value (p : ℕ) (a : ℝ) (J : Finset V → ℝ) :
    (exactEvaluator p (fun e => SpinGlass.Disorder.weight a (J e))).value =
      SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard p)
        (fun e => a*J e) := by
  rw [exactEvaluator, localEvaluator_value, ← SpinGlass.LocalCube.Gspin_eq_localGspin,
    SpinGlass.Mobius.Gspin, SpinGlass.Partition.normalizedPartition_eq_even_sum]
  simp only [Finset.subset_univ, Finset.filter_true]
  rw [SpinGlass.Expansion.graphical_expansion]
  rfl

/-- The exact branch's cost is counted by the same arithmetic evaluator. -/
theorem exactEvaluator_cost {p : ℕ} (hp : 0 < p) (weight : Finset V → ℝ) :
    (exactEvaluator p weight).operations ≤
      (p+6) * (Fintype.card V+1)^p * 2^(Fintype.card V) := by
  simpa only [exactEvaluator, Finset.card_univ] using localEvaluator_cost hp weight Finset.univ

end SpinGlass.SupportEvaluation
