import SpinGlass.SKPrimitiveAssembly
import SpinGlass.SKPrimitiveCatalogConnected

/-! # Exact finite enumeration of direct edges inside the candidate branch set -/
noncomputable section
namespace SpinGlass.SKDirectCatalog
open scoped BigOperators
open SKActualEvaluator SKFastEvaluator SKGraphMonomial SKCatalogSelection SKPrimitiveMonomials
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph consisting of the one specified direct branch edge. -/
def directGraph (A : Finset V) (p : Fin A.card × Fin A.card) : Finset (Finset V) :=
  {{branch A p.1, branch A p.2}}

/-- Direct graphs are enumerated by strictly ordered branch labels. -/
def directCatalog (A : Finset V) : Finset (Finset (Finset V)) :=
  (directPairs A.card).image (directGraph A)

/-- Each simple direct graph occurs once in that enumeration. -/
theorem directGraph_injOn (A : Finset V) :
    Set.InjOn (directGraph A) (directPairs A.card) := by
  intro p hp q hq heq
  have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hq' : q.1 < q.2 := (Finset.mem_filter.mp hq).2
  have he : tagVertices A (some p) = tagVertices A (some q) :=
    Finset.singleton_injective heq
  exact Option.some.inj (tagVertices_injective A (le_of_lt hp') (le_of_lt hq') he)

/-- Branch-pair factors in Algorithm 5 equal factors over actual distinct direct edges. -/
theorem direct_product_eq {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) :
    (∏ p ∈ directPairs A.card, (1 + direct (L := L) (branch A) f p.1 p.2)) =
      ∏ K ∈ directCatalog A, (1 + value id A (branch A) (totalColor A χ hL) f K) := by
  rw [directCatalog, Finset.prod_image (directGraph_injOn A)]
  apply Finset.prod_congr rfl
  intro p hp
  rw [directGraph, direct_value A χ hL f p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2)]

/-- Direct graphs have no outside vertices. -/
theorem direct_outside (A : Finset V) (p : Fin A.card × Fin A.card) :
    outside id A (directGraph A p) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvU, hvA⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvU
  have heq : e = {branch A p.1, branch A p.2} := Finset.mem_singleton.mp he
  simp only [id_eq, heq, Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with rfl | rfl <;> exact hvA (branch_mem A _)

/-- Direct catalog membership is exactly an unordered simple edge inside A. -/
theorem mem_directCatalog (A : Finset V) (K : Finset (Finset V)) :
    K ∈ directCatalog A ↔ ∃ a ∈ A, ∃ c ∈ A, a ≠ c ∧ K = {{a,c}} := by
  constructor
  · rintro hK
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
    exact ⟨branch A p.1, branch_mem A p.1, branch A p.2, branch_mem A p.2,
      fun h => (ne_of_lt (Finset.mem_filter.mp hp).2) (branch_injective A h), rfl⟩
  · rintro ⟨a,ha,c,hc,hac,rfl⟩
    obtain ⟨i,rfl⟩ := (branch_range A a).mp ha
    obtain ⟨j,rfl⟩ := (branch_range A c).mp hc
    have hij : i ≠ j := fun h => hac (congrArg (branch A) h)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i,j), by simpa [directPairs] using hlt, rfl⟩
    · exact Finset.mem_image.mpr ⟨(j,i), by simpa [directPairs] using hgt,
        by simp [directGraph, Finset.pair_comm]⟩

/-- Direct blocks have exactly the structural properties needed for optional graph products. -/
theorem direct_properties (A : Finset V) {K : Finset (Finset V)} (hK : K ∈ directCatalog A) :
    K.Nonempty ∧ SKBlockPartition.Connected id A K ∧
      (∀ e ∈ K, e.card = 2) ∧ SKBlockPartition.OutsideDegreeTwo id A K ∧ outside id A K = ∅ := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
  have hneq : branch A p.1 ≠ branch A p.2 :=
    fun h => (ne_of_lt (Finset.mem_filter.mp hp).2) (branch_injective A h)
  refine ⟨Finset.singleton_nonempty _, SKPrimitiveCatalogWalk.connected_singleton A _, ?_, ?_,
    direct_outside A p⟩
  · intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.card_pair hneq
  · intro v hv
    have hv' : v ∈ outside id A (directGraph A p) := hv
    rw [direct_outside] at hv'
    simp at hv'

end SpinGlass.SKDirectCatalog
