import SpinGlass.SKColorfulGraphSum
import SpinGlass.SKReferenceAggregation

/-! # Proposition 7.1: complete correctness of the actual colorful SK coefficient -/
noncomputable section
namespace SpinGlass.SKCoefficientCorrectness
open scoped BigOperators
open SKActualEvaluator SKGraphMonomial SKColorfulGraphSum
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Explicit membership in the complete finite even simple-graph family. -/
theorem evenGraphs_eq_filter : SpinGlass.SupportMassCounting.evenGraphs (V := V) 2 =
    (Finset.univ : Finset (Finset (Finset V))).filter
      (fun Γ => (∀ e ∈ Γ, e.card = 2) ∧ Expansion.IsEven id Γ) := by
  ext Γ
  simp [SpinGlass.SupportMassCounting.evenGraphs, Finset.subset_iff]

/-- All used nonbranch vertices of an even graph have exactly degree two. -/
theorem outside_degree_of_even_branch (A : Finset V) (Γ : Finset (Finset V))
    (heven : Expansion.IsEven id Γ) (hbranch : Hypergraph.branch Γ = A) :
    SKBlockPartition.OutsideDegreeTwo id A Γ := by
  intro v hv
  obtain ⟨hvU,hvA⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨e,he,hev⟩ := Finset.mem_biUnion.mp hvU
  apply SKComponents.outside_degree_two id Γ heven v _ ⟨e,he⟩ hev
  simpa [SKBranching.branchVertices_eq_branch, hbranch] using hvA

/-- The actual coordinate filter is precisely the stated even-graph predicate. -/
theorem coordinate_predicate_iff {L : ℕ} (A : Finset V) (χ : V → Fin L)
    (Γ : Finset (Finset V)) (k : Fin (L + 1)) (S : Finset (Fin L)) :
    (GraphCondition A Γ ∧ Γ.card = k.val ∧ colors id A χ Γ = S ∧
      Colorful id A χ Γ ∧ Accepts id (branch A) Γ) ↔
    ((∀ e ∈ Γ, e.card = 2) ∧ Expansion.IsEven id Γ) ∧
      Hypergraph.branch Γ = A ∧ Γ.card = k.val ∧ Colorful id A χ Γ ∧ colors id A χ Γ = S := by
  have ha (hd : SKBlockPartition.OutsideDegreeTwo id A Γ) :
      Accepts id (branch A) Γ ↔ Expansion.IsEven id Γ ∧ Hypergraph.branch Γ = A := by
    rw [accepts_iff_even_branch id A (branch A) Γ (branch_range A)]
    · rw [SKBranching.branchVertices_eq_branch]
    · intro v hvA
      by_cases hv : v ∈ outside id A Γ
      · exact Or.inr (hd v hv)
      · exact Or.inl (degree_zero_of_not_outside A Γ v hvA hv)
  constructor
  · rintro ⟨⟨hu,hd⟩,hk,hS,hc,hab⟩
    obtain ⟨he,hb⟩ := (ha hd).mp hab
    exact ⟨⟨hu,he⟩,hb,hk,hc,hS⟩
  · rintro ⟨⟨hu,he⟩,hb,hk,hc,hS⟩
    have hd := outside_degree_of_even_branch A Γ he hb
    exact ⟨⟨hu,hd⟩,hk,hS,hc,(ha hd).mpr ⟨he,hb⟩⟩

/-- End-to-end coefficient correctness: literal memoized tables, orientation
normalization, finite exponential, direct-edge product, and extraction all agree
with the claimed exact colorful graph sum. -/
theorem coefficient_eq_reference {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (k : Fin (L + 1)) (S : Finset (Fin L)) :
    SKActualEvaluator.coefficient A χ f k S =
      SKReferenceAggregation.graphCoefficientSum A (totalColor A χ hL) f k S := by
  rw [SKActualEvaluator.coefficient, evaluate_eq_graph_sum A χ hL f, SKRing.coeff_sum,
    Finset.sum_apply]
  simp_rw [value_coefficient]
  rw [SKReferenceAggregation.graphCoefficientSum, evenGraphs_eq_filter]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  have hp := coordinate_predicate_iff A (totalColor A χ hL) Γ k S
  simp only [← ite_and, hp]

/-- Outside colors determine both injectivity and color support; branch colors are ignored. -/
theorem colors_equal_of_outside {L : ℕ} (A : Finset V) (χ ψ : V → Fin L)
    (h : ∀ v, v ∉ A → χ v = ψ v) (Γ : Finset (Finset V)) :
    colors id A χ Γ = colors id A ψ Γ ∧
      (Colorful id A χ Γ ↔ Colorful id A ψ Γ) := by
  have heq : Set.EqOn χ ψ (outside id A Γ) := fun v hv => h v (Finset.mem_sdiff.mp hv).2
  constructor
  · exact Finset.image_congr (fun v hv => heq hv)
  · exact heq.injOn_iff

/-- Ambient input-color arrays restrict to the actual outside type without changing
any graph coefficient. -/
theorem coefficient_eq_ambient_reference {L : ℕ} (A : Finset V) (χ : V → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (k : Fin (L + 1)) (S : Finset (Fin L)) :
    SKActualEvaluator.coefficient A (fun v => χ v.val) f k S =
      SKReferenceAggregation.graphCoefficientSum A χ f k S := by
  rw [coefficient_eq_reference A (fun v => χ v.val) hL f k S]
  unfold SKReferenceAggregation.graphCoefficientSum
  apply Finset.sum_congr rfl
  intro Γ hΓ
  have hχ := colors_equal_of_outside A (totalColor A (fun v => χ v.val) hL) χ
    (fun v hv => by simp [totalColor,hv]) Γ
  rw [hχ.1, hχ.2]

/-- Returned support-size sums are the exact reference graph sums. -/
theorem byOutsideSize_eq_reference {L : ℕ} (A : Finset V) (χ : V → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (m : ℕ) :
    SKActualEvaluator.byOutsideSize A (fun v => χ v.val) f m =
      SKReferenceAggregation.byOutsideSize A χ f m := by
  unfold SKActualEvaluator.byOutsideSize SKFastEvaluator.byOutsideSize SKReferenceAggregation.byOutsideSize
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro S hS
  have he := coefficient_eq_ambient_reference A χ hL f k S
  exact congrArg (fun x : ℝ => if S.card = m then x else 0) he

/-- The complete implemented randomized SK estimator equals the already analyzed
actual graph estimator, with its bounded branch-set enumeration. -/
theorem estimator_eq_reference (D L R : ℕ) (hL : 0 < L)
    (χ : Finset V → Fin R → V → Fin L) (f : Finset V → ℝ) :
    SKActualEvaluator.estimator D L R χ f = SKReferenceAggregation.referenceEstimator D L R χ f := by
  unfold SKActualEvaluator.estimator SKReferenceAggregation.referenceEstimator
  simp_rw [byOutsideSize_eq_reference _ _ hL]

/-- The physical signed disorder input connects directly to the proved probability theorem. -/
theorem estimator_eq_disorder (D L R : ℕ) (hL : 0 < L)
    (χ : Finset V → Fin R → V → Fin L) (a : ℝ) (J : Finset V → ℝ) :
    SKActualEvaluator.estimator D L R χ (fun e => Real.tanh (a * J e)) =
      SKRandomMeanSquare.estimator D L R a χ J := by
  rw [estimator_eq_reference D L R hL]
  exact SKReferenceAggregation.referenceEstimator_disorder D L R χ a J

end SpinGlass.SKCoefficientCorrectness
