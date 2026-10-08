import SpinGlass.SKActualEvaluator
import SpinGlass.SKRandomMeanSquare

/-! Exact finite regrouping from graph-reference coefficients to the shared-color estimator. -/
noncomputable section
namespace SpinGlass.SKReferenceAggregation
open scoped BigOperators
open Finset
open SpinGlass.SKGraphMonomial SpinGlass.SKRandomMeanSquare
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The explicit graph reference for the coefficient in equation (75). -/
def graphCoefficientSum {L : ℕ} (A : Finset V) (χ : V → Fin L) (f : Finset V → ℝ)
    (k : Fin (L + 1)) (S : Finset (Fin L)) : ℝ :=
  ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
    if SpinGlass.Hypergraph.branch Γ = A ∧ Γ.card = k.val ∧
      Colorful id A χ Γ ∧ colors id A χ Γ = S then weight f Γ else 0

/-- The coefficient aggregation used by the actual evaluator, applied to graph references. -/
def byOutsideSize {L : ℕ} (A : Finset V) (χ : V → Fin L) (f : Finset V → ℝ) (m : ℕ) : ℝ :=
  ∑ k : Fin (L + 1), ∑ S : Finset (Fin L),
    if S.card = m then graphCoefficientSum A χ f k S else 0

/-- Injectivity of the outside colors identifies color-set size with vertex-set size. -/
theorem colorful_card {L : ℕ} (A : Finset V) (χ : V → Fin L) (Γ : Finset (Finset V))
    (hc : Colorful id A χ Γ) : (colors id A χ Γ).card = (outside id A Γ).card := by
  exact Finset.card_image_iff.mpr hc

/-- The reference coefficient is grouped by actual outside vertex count. -/
theorem byOutsideSize_eq {L : ℕ} (A : Finset V) (χ : V → Fin L) (f : Finset V → ℝ) (m : ℕ) :
    byOutsideSize A χ f m =
      ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
        if SpinGlass.Hypergraph.branch Γ = A ∧ Γ.card ≤ L ∧
          Colorful id A χ Γ ∧ (outside id A Γ).card = m then weight f Γ else 0 := by
  unfold byOutsideSize graphCoefficientSum
  have hi (S : Finset (Fin L)) (k : Fin (L + 1)) :
      (if S.card = m then ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
        if SpinGlass.Hypergraph.branch Γ = A ∧ Γ.card = k.val ∧
          Colorful id A χ Γ ∧ colors id A χ Γ = S then weight f Γ else 0 else 0) =
      ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
        if S.card = m then if SpinGlass.Hypergraph.branch Γ = A ∧ Γ.card = k.val ∧
          Colorful id A χ Γ ∧ colors id A χ Γ = S then weight f Γ else 0 else 0 := by
    by_cases h : S.card = m <;> simp [h]
  simp_rw [hi]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin L))))
    (t := SpinGlass.SupportMassCounting.evenGraphs (V := V) 2)]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (L + 1))))
    (t := SpinGlass.SupportMassCounting.evenGraphs (V := V) 2)]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hA : SpinGlass.Hypergraph.branch Γ = A
  · by_cases hc : Colorful id A χ Γ
    · by_cases hL : Γ.card ≤ L
      · let kΓ : Fin (L + 1) := ⟨Γ.card, by omega⟩
        have hk (k : Fin (L + 1)) : Γ.card = k.val ↔ k = kΓ := by
          constructor
          · intro h; exact Fin.ext h.symm
          · intro h; exact congrArg Fin.val h.symm
        have hcs := colorful_card A χ Γ hc
        simp only [hA, true_and, hc, hk, hL]
        rw [Finset.sum_eq_single kΓ]
        · simp only [ite_true]
          rw [Finset.sum_eq_single (colors id A χ Γ)]
          · simp [hcs]
          · intro S hS hne
            have hn : colors id A χ Γ ≠ S := Ne.symm hne
            simp [hn]
          · simp
        · intro k hk' hne
          simp [hne]
        · simp
      · have hk (k : Fin (L + 1)) : Γ.card ≠ k.val := by have := k.isLt; omega
        simp [hA, hc, hL, hk]
    · simp [hA, hc]
  · simp [hA]


/-- The literal inverse-probability coefficient of one actual outside coloring. -/
def singleCoefficient {L : ℕ} (A : Finset V) (χ : V → Fin L) (Γ : Finset (Finset V)) : ℝ :=
  SpinGlass.ColoringProbability.coefficient L (fun v : outside id A Γ => χ v)

theorem singleCoefficient_eq {L : ℕ} (A : Finset V) (χ : V → Fin L) (Γ : Finset (Finset V)) :
    singleCoefficient A χ Γ =
      (if Colorful id A χ Γ then 1 else 0) /
        SpinGlass.ColoringProbability.probability L (outside id A Γ).card := by
  have hi : Function.Injective (fun v : outside id A Γ => χ v) ↔ Colorful id A χ Γ := by
    constructor
    · intro h v hv u hu heq
      exact congrArg Subtype.val (h (show χ (⟨v, hv⟩ : outside id A Γ) = χ (⟨u, hu⟩ : outside id A Γ) from heq))
    · intro h v u heq
      exact Subtype.ext (h v.property u.property heq)
  simp [singleCoefficient, SpinGlass.ColoringProbability.coefficient,
    SpinGlass.ColoringProbability.indicator, hi]

/-- At the graph's actual branch set, the algorithmic outside support is the
same outside support used by the probability theorem. -/
theorem outside_at_branch (Γ : Finset (Finset V)) :
    outside id (SpinGlass.Hypergraph.branch Γ) Γ = outsideVertices Γ := rfl

/-- Summing the returned vector against its inverse colorful probability is
exactly one unbiased colorful graph-sum trial. -/
theorem weightedSizeSum_eq {L : ℕ} (A : Finset V) (χ : V → Fin L) (f : Finset V → ℝ) :
    (∑ m ∈ Finset.range (L + 1), (SpinGlass.ColoringProbability.probability L m)⁻¹ * byOutsideSize A χ f m) =
      ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
        if SpinGlass.Hypergraph.branch Γ = A ∧ Γ.card ≤ L then
          singleCoefficient A χ Γ * weight f Γ else 0 := by
  simp_rw [byOutsideSize_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hA : SpinGlass.Hypergraph.branch Γ = A
  · by_cases hL : Γ.card ≤ L
    · by_cases hc : Colorful id A χ Γ
      · have hcL : (outside id A Γ).card ≤ L := by
          rw [← colorful_card A χ Γ hc]
          simpa using Finset.card_le_univ (colors id A χ Γ)
        rw [Finset.sum_eq_single (outside id A Γ).card]
        · simp [hA, hL, hc, singleCoefficient_eq, div_eq_mul_inv]
        · intro m hm hne
          have hn : (outside id A Γ).card ≠ m := Ne.symm hne
          simp [hA, hL, hc, hn]
        · intro hn
          exact False.elim (hn (Finset.mem_range.mpr (by omega)))
      · simp [hA, hL, hc, singleCoefficient_eq]
    · simp [hA, hL]
  · simp [hA]


/-- The bounded-cardinality candidate schedule is the exact same finite family,
with no extra 2^N enumeration in its operational definition. -/
theorem candidate_sum (D : ℕ) (f : Finset V → ℝ) :
    (∑ b ∈ Finset.range (D + 1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b, f A) =
      ∑ A ∈ (Finset.univ : Finset V).powerset.filter (fun A => A.card ≤ D), f A := by
  have h := Finset.sum_fiberwise_eq_sum_filter ((Finset.univ : Finset V).powerset)
    (Finset.range (D + 1)) Finset.card f
  simpa only [← Finset.powersetCard_eq_filter, Finset.mem_range, Nat.lt_succ_iff] using h

/-- Inverse-probability averaging is exactly the graph coefficient used in Parseval. -/
theorem graphCoefficient_eq_trials (L R : ℕ) (χ : Colors V L R) (Γ : Finset (Finset V)) :
    SpinGlass.ColoringEstimator.graphCoefficient outsideVertices SpinGlass.Hypergraph.branch L R χ Γ =
      (R : ℝ)⁻¹ * ∑ r : Fin R, singleCoefficient (SpinGlass.Hypergraph.branch Γ)
        (χ (SpinGlass.Hypergraph.branch Γ) r) Γ := rfl

/-- One candidate branch set's repeated reference aggregation. -/
theorem averageSizeSum_eq (L R : ℕ) (A : Finset V) (χ : Colors V L R) (f : Finset V → ℝ) :
    (R : ℝ)⁻¹ * (∑ r : Fin R, ∑ m ∈ Finset.range (L + 1),
      (SpinGlass.ColoringProbability.probability L m)⁻¹ * byOutsideSize A (χ A r) f m) =
      ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
        if SpinGlass.Hypergraph.branch Γ = A ∧ Γ.card ≤ L then
          ((R : ℝ)⁻¹ * ∑ r : Fin R, singleCoefficient A (χ A r) Γ) * weight f Γ else 0 := by
  simp_rw [weightedSizeSum_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hk : SpinGlass.Hypergraph.branch Γ = A ∧ Γ.card ≤ L
  · simp only [hk, and_self, if_true]
    rw [← Finset.sum_mul]
    ring
  · simp [hk]

/-- Actual Algorithm 2 aggregation, with graph-reference coefficients replacing
only the coefficient evaluator. -/
def referenceEstimator (D L R : ℕ) (χ : Colors V L R) (f : Finset V → ℝ) : ℝ :=
  ∑ b ∈ Finset.range (D + 1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b,
    (R : ℝ)⁻¹ * ∑ r : Fin R, ∑ m ∈ Finset.range (L + 1),
      (SpinGlass.ColoringProbability.probability L m)⁻¹ * byOutsideSize A (χ A r) f m

/-- Full finite regrouping from coordinate extraction, inverse probabilities,
repetitions, and candidate sets to the signed shared-color graph-sum semantics. -/
theorem referenceEstimator_eq (D L R : ℕ) (χ : Colors V L R) (f : Finset V → ℝ) :
    referenceEstimator D L R χ f =
      ∑ Γ ∈ SpinGlass.SupportMassCounting.evenGraphs (V := V) 2,
        SpinGlass.SKRandomMeanSquare.coefficient D L R χ Γ * weight f Γ := by
  unfold referenceEstimator
  rw [candidate_sum]
  simp_rw [averageSizeSum_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hL : Γ.card ≤ L
  · by_cases hD : (SpinGlass.Hypergraph.branch Γ).card ≤ D
    · have hmem : SpinGlass.Hypergraph.branch Γ ∈
          (Finset.univ : Finset V).powerset.filter (fun A => A.card ≤ D) := by simp [hD]
      rw [Finset.sum_eq_single (SpinGlass.Hypergraph.branch Γ)]
      · simp only [hL, and_self, if_true, SpinGlass.SKRandomMeanSquare.coefficient,
          Retained, hD]
        rw [graphCoefficient_eq_trials]
      · intro A hA hne
        have hn : SpinGlass.Hypergraph.branch Γ ≠ A := Ne.symm hne
        simp [hn]
      · exact fun hn => False.elim (hn hmem)
    · have hz : SpinGlass.SKRandomMeanSquare.coefficient D L R χ Γ = 0 := by
        simp [SpinGlass.SKRandomMeanSquare.coefficient, Retained, hD]
      rw [hz, zero_mul]
      apply Finset.sum_eq_zero
      intro A hA
      have hn : SpinGlass.Hypergraph.branch Γ ≠ A := by
        intro h
        exact hD (h.symm ▸ (Finset.mem_filter.mp hA).2)
      simp [hn]
  · simp [hL, SpinGlass.SKRandomMeanSquare.coefficient, Retained]

/-- Physical signed weights identify this reference aggregation with the exact
estimator whose product-law MSE and logarithmic accuracy have been proved. -/
theorem referenceEstimator_disorder (D L R : ℕ) (χ : Colors V L R) (a : ℝ)
    (J : Finset V → ℝ) :
    referenceEstimator D L R χ (fun e => SpinGlass.Disorder.weight a (J e)) =
      SpinGlass.SKRandomMeanSquare.estimator D L R a χ J := by
  rw [referenceEstimator_eq]
  rfl

end SpinGlass.SKReferenceAggregation
