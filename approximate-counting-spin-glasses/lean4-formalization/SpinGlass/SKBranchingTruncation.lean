import SpinGlass.SKBranchingTail
import SpinGlass.DisorderLowerTail
import SpinGlass.DisorderUniform

/-! The actual SK branching-and-edge truncation and its exact mean-square error. -/
noncomputable section
namespace SpinGlass.SKBranching
open MeasureTheory Finset Real
open scoped BigOperators
open SpinGlass.Expansion SpinGlass.Disorder
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The manuscript's actual signed polynomial with both branching and edge cutoffs. -/
def skTruncation (D L : ℕ) (a : ℝ) (J : Finset V → ℝ) : ℝ :=
  ∑ Γ ∈ (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
    (fun Γ => (SpinGlass.Hypergraph.branch Γ).card ≤ D ∧ Γ.card ≤ L),
      monomial (fun _ => a) Γ J

/-- Overlap of the two omitted families causes no difficulty: every coefficient
mass is nonnegative and the sum of the two omissions is an upper bound. -/
theorem joint_omitted_mass_le (D L : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∑ Γ ∈ (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
      (fun Γ => ¬((SpinGlass.Hypergraph.branch Γ).card ≤ D ∧ Γ.card ≤ L)), r ^ Γ.card) ≤
      branchTail (V := V) D r +
        ∑ Γ ∈ (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
          (fun Γ => L + 1 ≤ Γ.card), r ^ Γ.card := by
  unfold branchTail
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro Γ hΓ
  by_cases hD : (SpinGlass.Hypergraph.branch Γ).card ≤ D
  · have hDb : ¬ D < (SpinGlass.Hypergraph.branch Γ).card := by omega
    by_cases hL : Γ.card ≤ L
    · have hLb : ¬ L + 1 ≤ Γ.card := by omega
      simp [hD, hDb, hL, hLb]
    · have hLb : L + 1 ≤ Γ.card := by omega
      simp [hD, hDb, hL, hLb]
  · have hDb : D < (SpinGlass.Hypergraph.branch Γ).card := by omega
    by_cases hL : L + 1 ≤ Γ.card
    · simp only [hD, false_and, not_false_eq_true, if_true, hDb, hL]
      split_ifs <;> linarith [pow_nonneg hr Γ.card]
    · simp [hD, hDb, hL]

/-- Exact Parseval formula for the real iid-disorder error of the signed SK truncation. -/
theorem skTruncation_mse_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (D L : ℕ) (a : ℝ) :
    (∫ J, (SpinGlass.Partition.normalizedPartition id
        ((Finset.univ : Finset V).powersetCard 2) (fun e => a * J e) -
      skTruncation D L a J) ^ 2 ∂iidLaw μ) =
      ∑ Γ ∈ (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
        (fun Γ => ¬((SpinGlass.Hypergraph.branch Γ).card ≤ D ∧ Γ.card ≤ L)),
          secondMoment μ a ^ Γ.card := by
  simp_rw [SpinGlass.Partition.normalizedPartition_eq_even_sum]
  simpa only [skTruncation, monomial, weight, one_mul, one_pow, Finset.prod_const] using
    retained_polynomial_error μ hμ (fun _ : Finset V => a)
      (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id))
      (fun _ => 1) (fun Γ => (SpinGlass.Hypergraph.branch Γ).card ≤ D ∧ Γ.card ≤ L)

/-- Mean-square truncation error is bounded by the actual branching tail plus the
proved uniform edge tail. Only the disorder symmetry and its true second moment enter. -/
theorem skTruncation_mse_le_branchTail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (D L : ℕ) (a : ℝ) (hV : 2 ≤ Fintype.card V)
    {vplus q : ℝ} (hvplus : 0 ≤ vplus)
    (hvT : vplus < SpinGlass.UniformMassEntropy.thresholdSquared 2)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hrq : secondMoment μ a ≤ q * (vplus / (Fintype.card V : ℝ))) :
    (∫ J, (SpinGlass.Partition.normalizedPartition id
        ((Finset.univ : Finset V).powersetCard 2) (fun e => a * J e) -
      skTruncation D L a J) ^ 2 ∂iidLaw μ) ≤
      branchTail (V := V) D (secondMoment μ a) +
        SpinGlass.UniformMass.massConstant 2 vplus * q ^ (L + 1) := by
  rw [skTruncation_mse_eq μ hμ]
  apply (joint_omitted_mass_le D L (secondMoment_nonneg μ a)).trans
  apply add_le_add le_rfl
  exact SpinGlass.UniformMass.graphical_edge_tail_nat (by omega : 0 < 2) hV
    hvplus hvT (secondMoment_nonneg μ a) hq hq1 (by simpa using hrq) (L + 1)


/-- Proposition 6.2: the complete actual iid mean-square error, with both cutoffs,
all three exact terms, and no assumed graph-mass or Parseval conclusions. -/
theorem skTruncation_mse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) {N D L : ℕ} (hcard : Fintype.card V = N) (hN : 2 ≤ N)
    (a : ℝ) {B vplus q alpha : ℝ} (hB : 0 ≤ B) (hB1 : B < 1)
    (hrB : secondMoment μ a ≤ B ^ 2 / (N : ℝ))
    (hvplus : 0 ≤ vplus) (hvT : vplus < SpinGlass.UniformMassEntropy.thresholdSquared 2)
    (hq : 0 < q) (hq1 : q ≤ 1) (hrq : secondMoment μ a ≤ q * (vplus / (N : ℝ)))
    (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (max 1 (SpinGlass.SKBranchingScalar.branchConstant B) * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * N)) :
    (∫ J, (SpinGlass.Partition.normalizedPartition id
        ((Finset.univ : Finset V).powersetCard 2) (fun e => a * J e) -
      skTruncation D L a J) ^ 2 ∂iidLaw μ) ≤
      SpinGlass.UniformMass.massConstant 2 vplus * q ^ (L + 1) +
      2 * SpinGlass.SKBranchingScalar.massConstant B *
        Real.exp (-SpinGlass.CutoffTail.phi 1
          (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N (D + 1)) +
      SpinGlass.UniformMass.massConstant 2 vplus *
        Real.exp (-(2 * alpha * Real.log (1 / q)) * (N : ℝ)) := by
  have hb := branch_truncation_tail hcard hN hB hB1 (secondMoment_nonneg μ a) hrB
    hvplus hvT hq hq1 hrq halpha hgap hcut
  have hm := skTruncation_mse_le_branchTail μ hμ D L a (by omega : 2 ≤ Fintype.card V)
    hvplus hvT hq.le hq1 (by simpa only [hcard] using hrq)
  exact hm.trans (by linarith)

/-- The physical SK normalization satisfies the uniform second-moment bound,
using exactly symmetry and variance one of the original real disorder. -/
theorem sk_physical_secondMoment_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) {N : ℕ} (hN : 0 < N)
    {β B : ℝ} (hβ : 0 ≤ β) (hβB : β ≤ B) :
    secondMoment μ (pureScale N 2 β) ≤ B ^ 2 / (N : ℝ) := by
  apply (secondMoment_le_scale_sq μ hunit _).trans
  rw [pureScale_sq hN]
  simp only [Nat.reduceSub, pow_one]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hβ hβB 2) (Nat.cast_nonneg _)

/-- The manuscript's physical SK truncation estimate uniformly in 0≤β≤B, with
q=(B/βplus)^2 and no separate second-moment or mass assumptions. -/
theorem sk_physical_truncation_mse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N D L : ℕ} (hN : 2 ≤ N)
    {β B βplus alpha : ℝ} (hβ : 0 ≤ β) (hβB : β ≤ B)
    (hB : 0 < B) (hB1 : B < 1) (hBplus : B < βplus)
    (hplusT : βplus ^ 2 < SpinGlass.UniformMassEntropy.thresholdSquared 2)
    (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (max 1 (SpinGlass.SKBranchingScalar.branchConstant B) * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * N)) :
    (∫ J, (SpinGlass.Partition.normalizedPartition id
        ((Finset.univ : Finset (Fin N)).powersetCard 2) (fun e => pureScale N 2 β * J e) -
      skTruncation D L (pureScale N 2 β) J) ^ 2 ∂iidLaw μ) ≤
      SpinGlass.UniformMass.massConstant 2 (βplus ^ 2) * ((B / βplus) ^ 2) ^ (L + 1) +
      2 * SpinGlass.SKBranchingScalar.massConstant B *
        Real.exp (-SpinGlass.CutoffTail.phi 1
          (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N (D + 1)) +
      SpinGlass.UniformMass.massConstant 2 (βplus ^ 2) *
        Real.exp (-(2 * alpha * Real.log (1 / (B / βplus) ^ 2)) * (N : ℝ)) := by
  have hNpos : 0 < N := by omega
  have hplus := hB.trans hBplus
  have hq : 0 < (B / βplus) ^ 2 := pow_pos (div_pos hB hplus) _
  have hq1 : (B / βplus) ^ 2 ≤ 1 := by
    exact (pow_lt_one₀ (div_nonneg hB.le hplus.le) ((div_lt_one hplus).mpr hBplus) (by omega : 2 ≠ 0)).le
  have hrB := sk_physical_secondMoment_le μ hunit hNpos hβ hβB
  have hrq : secondMoment μ (pureScale N 2 β) ≤ (B / βplus) ^ 2 * (βplus ^ 2 / (N : ℝ)) := by
    convert hrB using 1
    field_simp [hplus.ne']
  exact skTruncation_mse μ hμ (Fintype.card_fin N) hN (pureScale N 2 β)
    hB.le hB1 hrB (sq_nonneg _) hplusT hq hq1 hrq halpha hgap hcut

end SpinGlass.SKBranching
