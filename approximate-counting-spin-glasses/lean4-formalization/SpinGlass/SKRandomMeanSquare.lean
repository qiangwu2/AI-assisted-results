import SpinGlass.SKBranchingTruncation
import SpinGlass.ColoringEstimator
import SpinGlass.DisorderIndependentCoefficients
import SpinGlass.FiniteProbability
import SpinGlass.SupportMassCounting

/-! The actual shared-color estimator on independent color and real-disorder laws. -/
noncomputable section
namespace SpinGlass.SKRandomMeanSquare
open MeasureTheory Finset Real
open scoped BigOperators
open SpinGlass.Disorder SpinGlass.ColoringEstimator
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Colors (V : Type*) (L R : ℕ) := SpinGlass.ColoringEstimator.Colors V (Finset V) L R

/-- Exactly the vertices colored for each graph by its branching-set trial array. -/
def outsideVertices (Γ : Finset (Finset V)) : Finset V :=
  SpinGlass.Hypergraph.support Γ \ SpinGlass.Hypergraph.branch Γ

def Retained (D L : ℕ) (Γ : Finset (Finset V)) : Prop :=
  (SpinGlass.Hypergraph.branch Γ).card ≤ D ∧ Γ.card ≤ L

instance (D L : ℕ) (Γ : Finset (Finset V)) : Decidable (Retained D L Γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- One independent uniform color array for every proposed branch set and repetition. -/
def colorLaw (V : Type*) [Fintype V] [DecidableEq V] (L R : ℕ) : Measure (Colors V L R) :=
  SpinGlass.FiniteProbability.uniformLaw (Colors V L R)

/-- Coefficients on the full graph universe vanish precisely on omitted graphs. -/
def coefficient (D L R : ℕ) (χ : Colors V L R) (Γ : Finset (Finset V)) : ℝ :=
  if Retained D L Γ then
    graphCoefficient outsideVertices SpinGlass.Hypergraph.branch L R χ Γ else 0

/-- The actual signed graph-sum randomized estimator, using shared vertex colors. -/
def estimator (D L R : ℕ) (a : ℝ) (χ : Colors V L R) (J : Finset V → ℝ) : ℝ :=
  ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
    coefficient D L R χ Γ * monomial (fun _ => a) Γ J

/-- Retained outside vertex sets fit in the chosen palette. -/
theorem retained_outside_card (D L : ℕ) {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2) (hkeep : Retained D L Γ) :
    (outsideVertices Γ).card ≤ L := by
  have h := SpinGlass.SupportMassCounting.twice_support_le_edges hΓ
  exact (Finset.card_le_card (Finset.sdiff_subset)).trans (by dsimp [Retained] at hkeep; omega)

/-- Actual coefficient variance under the finite uniform law, including zero
coefficients on discarded graphs. -/
theorem coefficient_error_integral (D : ℕ) {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    {Γ : Finset (Finset V)} (hΓ : Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2) :
    (∫ χ : Colors V L R, (1 - coefficient D L R χ Γ) ^ 2 ∂colorLaw V L R) =
      if Retained D L Γ then
        (1 - SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card) /
          ((R : ℝ) * SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card)
      else 1 := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  unfold colorLaw
  rw [SpinGlass.FiniteProbability.integral_uniformLaw]
  by_cases hk : Retained D L Γ
  · simp only [coefficient, if_pos hk]
    have hs : (fun χ : Colors V L R =>
        (1 - graphCoefficient outsideVertices SpinGlass.Hypergraph.branch L R χ Γ) ^ 2) =
        (fun χ => (graphCoefficient outsideVertices SpinGlass.Hypergraph.branch L R χ Γ - 1) ^ 2) := by
      funext χ
      ring
    rw [hs]
    exact mean_graphCoefficient_variance outsideVertices SpinGlass.Hypergraph.branch hL hR Γ
      (retained_outside_card D L hΓ hk)
  · simp [coefficient, hk, SpinGlass.ColoringProbability.mean, ne_of_gt (Nat.cast_pos.mpr hL : (0 : ℝ) < L)]


instance colorLaw_probability {L R : ℕ} [Nonempty (Fin L)] :
    IsProbabilityMeasure (colorLaw V L R) := by
  unfold colorLaw
  infer_instance

/-- The error is exactly one polynomial on the full even-graph family. -/
theorem error_polynomial (D L R : ℕ) (a : ℝ) (χ : Colors V L R) (J : Finset V → ℝ) :
    SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard 2)
      (fun e => a * J e) - estimator D L R a χ J =
      ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
        (1 - coefficient D L R χ Γ) * monomial (fun _ => a) Γ J := by
  rw [SpinGlass.Partition.normalizedPartition_eq_even_sum]
  simp only [estimator, sub_mul, one_mul, Finset.sum_sub_distrib,
    SpinGlass.SupportMassCounting.evenGraphs, monomial, weight]

/-- The actual joint color/disorder squared error is integrable; the MSE is not
an integral that has silently defaulted to zero. -/
theorem error_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (D : ℕ) {L R : ℕ} (hL : 0 < L) (a : ℝ) :
    Integrable (fun χJ : Colors V L R × (Finset V → ℝ) =>
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard 2)
        (fun e => a * χJ.2 e) - estimator D L R a χJ.1 χJ.2) ^ 2)
      ((colorLaw V L R).prod (iidLaw μ)) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  simp_rw [error_polynomial]
  exact integrable_independent_polynomial_square μ (colorLaw V L R) (fun _ => a)
    (SpinGlass.SupportMassCounting.evenGraphs (V := V) 2) (fun χ Γ => 1 - coefficient D L R χ Γ)
    (fun Γ _ => measurable_of_countable _) (fun Γ _ => Integrable.of_finite)

/-- Exact MSE on the actual product probability space, allowing every correlation
between graph indicators caused by the shared color arrays. -/
theorem mse_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (D : ℕ) {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (a : ℝ) :
    (∫ χJ : Colors V L R × (Finset V → ℝ),
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard 2)
        (fun e => a * χJ.2 e) - estimator D L R a χJ.1 χJ.2) ^ 2
      ∂(colorLaw V L R).prod (iidLaw μ)) =
      ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
        (if Retained D L Γ then
          (1 - SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card) /
            ((R : ℝ) * SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card)
         else 1) * secondMoment μ a ^ Γ.card := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  simp_rw [error_polynomial]
  rw [independent_coefficients_second_moment μ hμ (colorLaw V L R) (fun _ => a)
    (SpinGlass.SupportMassCounting.evenGraphs (V := V) 2) (fun χ Γ => 1 - coefficient D L R χ Γ)
    (fun Γ _ => measurable_of_countable _) (fun Γ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [coefficient_error_integral D hL hR hΓ, Finset.prod_const]

/-- The omitted and retained graph coefficients are orthogonal, giving an exact
sum of truncation MSE and color variance with no factor two. -/
theorem mse_split (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (D : ℕ) {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (a : ℝ) :
    (∫ χJ : Colors V L R × (Finset V → ℝ),
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard 2)
        (fun e => a * χJ.2 e) - estimator D L R a χJ.1 χJ.2) ^ 2
      ∂(colorLaw V L R).prod (iidLaw μ)) =
      (∫ J, (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard 2)
        (fun e => a * J e) - SpinGlass.SKBranching.skTruncation D L a J) ^ 2 ∂iidLaw μ) +
      ∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs (V := V) 2).filter (Retained D L),
        ((1 - SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card) /
          ((R : ℝ) * SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card)) *
            secondMoment μ a ^ Γ.card := by
  rw [mse_eq μ hμ D hL hR, SpinGlass.SKBranching.skTruncation_mse_eq μ hμ]
  change (∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2, _) =
    (∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs (V := V) 2).filter (fun Γ => ¬Retained D L Γ), _) + _
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hk : Retained D L Γ <;> simp [hk]

/-- The actual color variance is bounded by the retained mass, then by C_+. -/
theorem color_variance_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (D : ℕ) {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (a : ℝ)
    (hV : 2 ≤ Fintype.card V) {vplus q : ℝ} (hvplus : 0 ≤ vplus)
    (hvT : vplus < SpinGlass.UniformMassEntropy.thresholdSquared 2)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hrq : secondMoment μ a ≤ q * (vplus / (Fintype.card V : ℝ))) :
    (∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs (V := V) 2).filter (Retained D L),
      ((1 - SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card) /
        ((R : ℝ) * SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card)) *
          secondMoment μ a ^ Γ.card) ≤
      SpinGlass.UniformMass.massConstant 2 vplus * (Real.exp (L : ℝ) / (R : ℝ)) := by
  have hc : ∀ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs (V := V) 2).filter (Retained D L),
      (1 - SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card) /
        ((R : ℝ) * SpinGlass.ColoringProbability.probability L (outsideVertices Γ).card) ≤
      Real.exp (L : ℝ) / (R : ℝ) := by
    intro Γ hΓ
    have hk := Finset.mem_filter.mp hΓ
    have hcard := retained_outside_card D L hk.1 hk.2
    have h := mean_graphCoefficient_variance_le outsideVertices SpinGlass.Hypergraph.branch hL hR Γ hcard
    rw [mean_graphCoefficient_variance outsideVertices SpinGlass.Hypergraph.branch hL hR Γ hcard] at h
    exact h
  have hr := secondMoment_nonneg μ a
  have hnon : 0 ≤ Real.exp (L : ℝ) / (R : ℝ) := div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)
  have hm : (∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
      secondMoment μ a ^ Γ.card) ≤ SpinGlass.UniformMass.massConstant 2 vplus := by
    simpa [SpinGlass.SupportMassCounting.evenGraphs] using
      SpinGlass.UniformMass.graphical_edge_tail_nat (V := V) (by omega : 0 < 2) hV hvplus hvT hr hq hq1
        (by simpa using hrq) 0
  calc
    _ ≤ ∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs (V := V) 2).filter (Retained D L),
        (Real.exp (L : ℝ) / (R : ℝ)) * secondMoment μ a ^ Γ.card := by
      exact Finset.sum_le_sum (fun Γ hΓ => mul_le_mul_of_nonneg_right (hc Γ hΓ) (pow_nonneg hr _))
    _ = (Real.exp (L : ℝ) / (R : ℝ)) *
        ∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs (V := V) 2).filter (Retained D L),
          secondMoment μ a ^ Γ.card := by rw [Finset.mul_sum]
    _ ≤ (Real.exp (L : ℝ) / (R : ℝ)) *
        ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2, secondMoment μ a ^ Γ.card := by
      apply mul_le_mul_of_nonneg_left _ hnon
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun Γ _ _ => pow_nonneg hr _)
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm hnon


/-- The complete four-term SK mean-square bound for the actual shared-color estimator. -/
theorem mse_four_terms (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    {N D L R : ℕ} (hcard : Fintype.card V = N) (hN : 2 ≤ N)
    (hL : 0 < L) (hR : 0 < R) (a : ℝ) {B vplus q alpha : ℝ}
    (hB : 0 ≤ B) (hB1 : B < 1) (hrB : secondMoment μ a ≤ B ^ 2 / (N : ℝ))
    (hvplus : 0 ≤ vplus) (hvT : vplus < SpinGlass.UniformMassEntropy.thresholdSquared 2)
    (hq : 0 < q) (hq1 : q ≤ 1) (hrq : secondMoment μ a ≤ q * (vplus / (N : ℝ)))
    (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (max 1 (SpinGlass.SKBranchingScalar.branchConstant B) * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * N)) :
    (∫ χJ : Colors V L R × (Finset V → ℝ),
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard 2)
        (fun e => a * χJ.2 e) - estimator D L R a χJ.1 χJ.2) ^ 2
      ∂(colorLaw V L R).prod (iidLaw μ)) ≤
      SpinGlass.UniformMass.massConstant 2 vplus * q ^ (L + 1) +
      2 * SpinGlass.SKBranchingScalar.massConstant B *
        Real.exp (-SpinGlass.CutoffTail.phi 1
          (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N (D + 1)) +
      SpinGlass.UniformMass.massConstant 2 vplus *
        Real.exp (-(2 * alpha * Real.log (1 / q)) * (N : ℝ)) +
      SpinGlass.UniformMass.massConstant 2 vplus * (Real.exp (L : ℝ) / (R : ℝ)) := by
  rw [mse_split μ hμ D hL hR a]
  exact add_le_add
    (SpinGlass.SKBranching.skTruncation_mse μ hμ hcard hN a hB hB1 hrB hvplus hvT
      hq hq1 hrq halpha hgap hcut)
    (color_variance_le μ D hL hR a (by omega : 2 ≤ Fintype.card V) hvplus hvT hq.le hq1
      (by simpa only [hcard] using hrq))

/-- The paper's exact physical SK four-term bound, under the original iid
symmetric variance-one disorder assumptions and uniformly in 0≤β≤B. -/
theorem physical_mse_four_terms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N D L R : ℕ} (hN : 2 ≤ N)
    (hL : 0 < L) (hR : 0 < R) {β B βplus alpha : ℝ}
    (hβ : 0 ≤ β) (hβB : β ≤ B) (hB : 0 < B) (hB1 : B < 1) (hBplus : B < βplus)
    (hplusT : βplus ^ 2 < SpinGlass.UniformMassEntropy.thresholdSquared 2)
    (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (max 1 (SpinGlass.SKBranchingScalar.branchConstant B) * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * N)) :
    (∫ χJ : Colors (Fin N) L R × (Finset (Fin N) → ℝ),
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard 2)
        (fun e => pureScale N 2 β * χJ.2 e) -
          estimator D L R (pureScale N 2 β) χJ.1 χJ.2) ^ 2
      ∂(colorLaw (Fin N) L R).prod (iidLaw μ)) ≤
      SpinGlass.UniformMass.massConstant 2 (βplus ^ 2) * ((B / βplus) ^ 2) ^ (L + 1) +
      2 * SpinGlass.SKBranchingScalar.massConstant B *
        Real.exp (-SpinGlass.CutoffTail.phi 1
          (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N (D + 1)) +
      SpinGlass.UniformMass.massConstant 2 (βplus ^ 2) *
        Real.exp (-(2 * alpha * Real.log (1 / (B / βplus) ^ 2)) * (N : ℝ)) +
      SpinGlass.UniformMass.massConstant 2 (βplus ^ 2) * (Real.exp (L : ℝ) / (R : ℝ)) := by
  have hNpos : 0 < N := by omega
  have hplus := hB.trans hBplus
  have hq : 0 < (B / βplus) ^ 2 := pow_pos (div_pos hB hplus) _
  have hq1 : (B / βplus) ^ 2 ≤ 1 := by
    exact (pow_lt_one₀ (div_nonneg hB.le hplus.le) ((div_lt_one hplus).mpr hBplus) (by omega : 2 ≠ 0)).le
  have hrB := SpinGlass.SKBranching.sk_physical_secondMoment_le μ hunit hNpos hβ hβB
  have hrq : secondMoment μ (pureScale N 2 β) ≤ (B / βplus) ^ 2 * (βplus ^ 2 / (N : ℝ)) := by
    convert hrB using 1
    field_simp [hplus.ne']
  exact mse_four_terms μ hμ (Fintype.card_fin N) hN hL hR (pureScale N 2 β)
    hB.le hB1 hrB (sq_nonneg _) hplusT hq hq1 hrq halpha hgap hcut

end SpinGlass.SKRandomMeanSquare
