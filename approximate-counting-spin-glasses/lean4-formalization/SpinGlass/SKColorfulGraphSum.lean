import SpinGlass.SKDirectCatalog
import SpinGlass.SKGraphProduct
import SpinGlass.SKCatalogMembership

/-! # Exact graph sum computed by the colorful SK evaluator -/
noncomputable section
namespace SpinGlass.SKColorfulGraphSum
open scoped BigOperators
open SKRing SKGraphMonomial SKActualEvaluator SKFastEvaluator SKCatalogSelection
open SKDirectCatalog SKCatalogMembership SKPrimitiveAssembly SKGraphProduct
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- All actual primitive graphs and all distinct direct branch edges. -/
def fullCatalog {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) : Finset (Finset (Finset V)) :=
  catalog A χ ∪ directCatalog A

/-- Intrinsic block conditions, including the direct-edge case. -/
structure Piece (A : Finset V) (K : Finset (Finset V)) : Prop where
  nonempty : K.Nonempty
  connected : SKBlockPartition.Connected id A K
  uniform : ∀ e ∈ K, e.card = 2
  degree : SKBlockPartition.OutsideDegreeTwo id A K

/-- Empty outside support forces a connected nonempty simple block to be one direct edge. -/
theorem direct_of_piece (A : Finset V) (K : Finset (Finset V)) (hK : Piece A K)
    (hout : ¬ (outside id A K).Nonempty) : K ∈ directCatalog A := by
  obtain ⟨e,he⟩ := hK.nonempty
  have hea : e ⊆ A := by
    intro v hv
    by_contra ha
    exact hout ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨e,he,hv⟩,ha⟩⟩
  have hsingle := SKPrimitiveCatalog.direct_singleton hK.connected he hea
  obtain ⟨a,c,hac,heq⟩ := Finset.card_eq_two.mp (hK.uniform e he)
  apply (mem_directCatalog A K).mpr
  refine ⟨a, hea (by simp [heq]), c, hea (by simp [heq]), hac, ?_⟩
  simpa [heq] using hsingle

/-- The table catalogs contain exactly the colorful intrinsically valid pieces. -/
theorem fullCatalog_iff {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (K : Finset (Finset V)) : K ∈ fullCatalog A χ ↔
      Piece A K ∧ Colorful id A (totalColor A χ hL) K := by
  constructor
  · intro hK
    rcases Finset.mem_union.mp hK with hp | hd
    · obtain ⟨hp,hc⟩ := (catalog_iff A χ hL K).mp hp
      exact ⟨⟨hp.nonempty,hp.connected,hp.uniform,hp.degree⟩,hc⟩
    · obtain ⟨hne,hconn,hunif,hdeg,hout⟩ := direct_properties A hd
      refine ⟨⟨hne,hconn,hunif,hdeg⟩,?_⟩
      simp [Colorful,hout]
  · rintro ⟨hK,hc⟩
    by_cases hout : (outside id A K).Nonempty
    · exact Finset.mem_union_left _ ((catalog_iff A χ hL K).mpr
        ⟨⟨hK.nonempty,hK.connected,hK.uniform,hK.degree,hout⟩,hc⟩)
    · exact Finset.mem_union_right _ (direct_of_piece A K hK hout)

/-- The two supplied factor catalogs are genuinely disjoint. -/
theorem catalog_direct_disjoint {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) :
    Disjoint (catalog A χ) (directCatalog A) := by
  apply Finset.disjoint_left.mpr
  intro K hp hd
  have ho := (catalog_properties A χ hp).outside_nonempty
  have he := (direct_properties A hd).2.2.2.2
  change (outside id A K).Nonempty at ho
  rw [he] at ho
  exact Finset.not_nonempty_empty ho

/-- Actual graph condition before branch-degree extraction. -/
def GraphCondition (A : Finset V) (Γ : Finset (Finset V)) : Prop :=
  (∀ e ∈ Γ, e.card = 2) ∧ SKBlockPartition.OutsideDegreeTwo id A Γ

/-- For colorful graphs, the intrinsic graph condition and canonical catalog membership agree. -/
theorem builtFrom_iff_of_colorful {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (Γ : Finset (Finset V)) (hc : Colorful id A (totalColor A χ hL) Γ) :
    BuiltFrom id A (fullCatalog A χ) Γ ↔ GraphCondition A Γ := by
  constructor
  · intro hb
    have hp : ∀ K ∈ SKBlockPartition.blockFamily id A Γ, Piece A K :=
      fun K hK => ((fullCatalog_iff A χ hL K).mp (hb hK)).1
    constructor
    · intro e he
      have he' : e ∈ (SKBlockPartition.blockFamily id A Γ).biUnion id := by
        rw [SKBlockPartition.blockFamily_cover]; exact he
      obtain ⟨K,hK,heK⟩ := Finset.mem_biUnion.mp he'
      exact (hp K hK).uniform e heK
    · have hd := SKBlockPartition.union_outside_degree_two id A
        (SKBlockPartition.blockFamily id A Γ) (SKBlockPartition.canonical_valid id A Γ)
        (fun K hK => (hp K hK).degree)
      simpa only [SKBlockPartition.blockFamily_cover] using hd
  · rintro ⟨hunif,hdeg⟩ K hK
    apply (fullCatalog_iff A χ hL K).mpr
    refine ⟨⟨SKBlockPartition.blockFamily_nonempty id A Γ hK,
      SKBlockPartition.blockFamily_connected id A Γ hK,
      fun e he => hunif e (SKBlockPartition.blockFamily_subset id A Γ hK he),
      SKBlockPartition.block_outside_degree_two id A Γ hdeg hK⟩,?_⟩
    exact hc.mono (SKBlockPartition.outside_mono id A (SKBlockPartition.blockFamily_subset id A Γ hK))

/-- Graph values vanish on noncolorful graphs, irrespective of their decomposition. -/
theorem value_zero_of_not_colorful {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (f : E → ℝ) (Γ : Finset E)
    (hc : ¬ Colorful incidence A χ Γ) : value incidence A branch χ f Γ = 0 := by
  simp [value,hc]

/-- The complete optional factor product is the actual simple outside-degree-two graph sum. -/
theorem product_eq_graph_sum {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) :
    (∏ K ∈ fullCatalog A χ, (1 + value id A (branch A) (totalColor A χ hL) f K)) =
      ∑ Γ ∈ (Finset.univ : Finset (Finset (Finset V))).filter (GraphCondition A),
        value id A (branch A) (totalColor A χ hL) f Γ := by
  rw [optional_product_eq_graph_sum id A (branch A) (totalColor A χ hL) f (fullCatalog A χ)
    (fun K hK => ((fullCatalog_iff A χ hL K).mp hK).1.nonempty)
    (fun K hK => ((fullCatalog_iff A χ hL K).mp hK).1.connected)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hc : Colorful id A (totalColor A χ hL) Γ
  · rw [builtFrom_iff_of_colorful A χ hL Γ hc]
  · simp only [value_zero_of_not_colorful id A (branch A) (totalColor A χ hL) f Γ hc,
      ite_self]

/-- The actual recurrence, factorial, and direct-edge loops compute the exact graph sum. -/
theorem evaluate_eq_graph_sum {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) :
    SKActualEvaluator.evaluate A χ f =
      (∑ Γ ∈ (Finset.univ : Finset (Finset (Finset V))).filter (GraphCondition A),
        value id A (branch A) (totalColor A χ hL) f Γ).coeff := by
  rw [SKActualEvaluator.evaluate, evaluate_eq_polynomial, primitives_eq_catalog A χ hL f]
  rw [SKPrimitiveExpansion.exp_sum_sq_zero (catalog A χ)
    (fun K => value id A (branch A) (totalColor A χ hL) f K)
    (fun K hK => value_vanishesBelow id A (branch A) (totalColor A χ hL) f K
      (catalog_properties A χ hK).outside_nonempty)
    (fun K hK => value_sq_zero id A (branch A) (totalColor A χ hL) f K
      (catalog_properties A χ hK).outside_nonempty)]
  rw [direct_product_eq A χ hL f,
    ← Finset.prod_union (catalog_direct_disjoint A χ), ← fullCatalog, product_eq_graph_sum A χ hL f]

end SpinGlass.SKColorfulGraphSum
