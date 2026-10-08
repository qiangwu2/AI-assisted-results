import SpinGlass.SKBlockPartitionDegree
import SpinGlass.SKAttachments

/-! # Connectivity and traversal classification of actual primitive blocks

The graph here uses exactly the outside vertices incident to the selected block.
Connectivity is derived from the canonical edge relation, not supplied as an
additional hypothesis about a proposed traversal.
-/
noncomputable section
namespace SpinGlass.SKPrimitiveCatalog
open SimpleGraph SKComponents SKBlockPartition SKOutsideClassification
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def usedGraph (A : Finset V) (K : Finset (Finset V)) :
    SimpleGraph (outside id A K) := (graph K).induce (outside id A K : Set V)

theorem mem_outside_of_edge {A : Finset V} {K : Finset (Finset V)}
    {e : Finset V} (he : e ∈ K) {v : V} (hv : v ∈ e) (ha : v ∉ A) :
    v ∈ outside id A K :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨e, he, hv⟩, ha⟩

theorem pair_eq_of_mem {e : Finset V} (h2 : e.card = 2)
    {u v : V} (hu : u ∈ e) (hv : v ∈ e) (hne : u ≠ v) : ({u,v}:Finset V) = e := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact False.elim (hne rfl)
  · rfl
  · exact Finset.pair_comm _ _
  · exact False.elim (hne rfl)

theorem direct_singleton {A : Finset V} {K : Finset (Finset V)}
    (hc : SKBlockPartition.Connected id A K) {e : Finset V}
    (he : e ∈ K) (hea : e ⊆ A) : K = {e} := by
  have hs := direct_component_singleton id A K ⟨e,he⟩ hea
  apply Finset.Subset.antisymm
  · intro f hf
    have hm := (mem_component id A K ⟨e,he⟩ ⟨f,hf⟩).mpr (hc _ _)
    rw [hs, Finset.mem_singleton] at hm
    exact Finset.mem_singleton.mpr (congrArg Subtype.val hm)
  · exact Finset.singleton_subset_iff.mpr he

theorem same_edge_reachable (A : Finset V) (K : Finset (Finset V))
    (h2 : ∀ e ∈ K, e.card = 2) (e : K)
    (u v : outside id A K) (hu : u.val ∈ e.val) (hv : v.val ∈ e.val) :
    (usedGraph A K).Reachable u v := by
  by_cases h : u = v
  · subst v; exact .refl _
  · apply SimpleGraph.Adj.reachable
    have hne : u.val ≠ v.val := fun heq => h (Subtype.ext heq)
    change u.val ≠ v.val ∧ ({u.val,v.val}:Finset V) ∈ K
    exact ⟨hne, (pair_eq_of_mem (h2 e.val e.property) hu hv hne).symm ▸ e.property⟩

theorem related_reachable (A : Finset V) (K : Finset (Finset V))
    (h2 : ∀ e ∈ K, e.card = 2)
    (hout : ∀ e ∈ K, ∃ v ∈ e, v ∉ A)
    {e f : K} (hef : Related id A K e f) :
    ∀ u v : outside id A K, u.val ∈ e.val → v.val ∈ f.val →
      (usedGraph A K).Reachable u v := by
  induction hef with
  | rel e f h =>
    obtain ⟨w,hwA,hwe,hwf⟩ := h
    let w' : outside id A K := ⟨w,mem_outside_of_edge e.property hwe hwA⟩
    intro u v hu hv
    exact (same_edge_reachable A K h2 e u w' hu hwe).trans
      (same_edge_reachable A K h2 f w' v hwf hv)
  | refl e => exact fun u v hu hv => same_edge_reachable A K h2 e u v hu hv
  | symm e f h ih => exact fun u v hu hv => (ih v u hv hu).symm
  | trans e f g hef hfg ihef ihfg =>
    obtain ⟨w,hwf,hwA⟩ := hout f.val f.property
    let w' : outside id A K := ⟨w,mem_outside_of_edge f.property hwf hwA⟩
    intro u v hu hv
    exact (ihef u w' hu hwf).trans (ihfg w' v hwf hv)

theorem usedGraph_connected (A : Finset V) (K : Finset (Finset V))
    (hne : K.Nonempty) (hc : SKBlockPartition.Connected id A K)
    (h2 : ∀ e ∈ K, e.card = 2)
    (hout : ∀ e ∈ K, ∃ v ∈ e, v ∉ A) : (usedGraph A K).Connected := by
  obtain ⟨e,he⟩ := hne
  obtain ⟨w,hw,hwA⟩ := hout e he
  letI : Nonempty (outside id A K) := ⟨⟨w,mem_outside_of_edge he hw hwA⟩⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨eu,heu,hu⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp u.property).1
  obtain ⟨ev,hev,hv⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp v.property).1
  exact related_reachable A K h2 hout (hc ⟨eu,heu⟩ ⟨ev,hev⟩) u v hu hv

theorem usedGraph_degree_le_two (A : Finset V) (K : Finset (Finset V))
    (h2 : ∀ e ∈ K, e.card = 2) (hd : OutsideDegreeTwo id A K)
    (v : outside id A K) : ((usedGraph A K).neighborSet v).ncard ≤ 2 := by
  exact le_trans (induced_neighbor_card_le (graph K) _ v)
    (by rw [neighbor_card_eq_degree K h2, hd v.val v.property])

theorem usedGraph_neighbor_card (A : Finset V) (K : Finset (Finset V))
    (v : outside id A K) :
    ((usedGraph A K).neighborSet v).ncard =
      (((graph K).neighborSet v.val).toFinset.filter (fun w => w ∉ A)).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw
    have ha : (graph K).Adj v.val w.val := by
      simpa only [Set.mem_toFinset, mem_neighborSet, usedGraph, induce_adj] using hw
    exact Finset.mem_filter.mpr ⟨by simpa using ha, (Finset.mem_sdiff.mp w.property).2⟩
  · intro w hw w' hw' heq
    exact Subtype.ext heq
  · intro w hw
    obtain ⟨ha,hwA⟩ := Finset.mem_filter.mp hw
    have hadj : (graph K).Adj v.val w := by simpa using ha
    have hwS : w ∈ outside id A K := mem_outside_of_edge hadj.2 (by simp) hwA
    refine ⟨⟨w,hwS⟩, ?_, rfl⟩
    simpa only [Set.mem_toFinset, mem_neighborSet, usedGraph, induce_adj] using hadj

theorem usedGraph_add_attachments (A : Finset V) (K : Finset (Finset V))
    (h2 : ∀ e ∈ K, e.card = 2) (hd : OutsideDegreeTwo id A K)
    (v : outside id A K) :
    ((usedGraph A K).neighborSet v).ncard +
      (SKAttachments.attachments K A v.val).card = 2 := by
  rw [usedGraph_neighbor_card, SKAttachments.attachments, Nat.add_comm,
    Finset.card_filter_add_card_filter_not, ← Set.ncard_eq_toFinset_card',
    neighbor_card_eq_degree K h2, hd v.val v.property]

theorem mem_attachments (A : Finset V) (K : Finset (Finset V)) (v a : V) :
    a ∈ SKAttachments.attachments K A v ↔ a ∈ A ∧ v ≠ a ∧ ({v,a}:Finset V) ∈ K := by
  classical
  simp only [SKAttachments.attachments, Finset.mem_filter, Set.mem_toFinset,
    mem_neighborSet, graph]
  tauto

/-- The complete graph-theoretic alternative, with exact spanning equality. -/
theorem direct_or_traversal (A : Finset V) (K : Finset (Finset V))
    (hne : K.Nonempty) (hc : SKBlockPartition.Connected id A K)
    (h2 : ∀ e ∈ K, e.card = 2) (hd : OutsideDegreeTwo id A K) :
    (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ K = {{a,b}}) ∨
    ((∀ e ∈ K, ∃ v ∈ e, v ∉ A) ∧
      ((∃ (u v : outside id A K) (p : (usedGraph A K).Walk u v),
        p.IsPath ∧ (∀ x, x ∈ p.support) ∧ usedGraph A K = p.toSubgraph.spanningCoe) ∨
       (∃ (u : outside id A K) (p : (usedGraph A K).Walk u u),
        p.IsCycle ∧ (∀ x, x ∈ p.support) ∧ usedGraph A K = p.toSubgraph.spanningCoe))) := by
  classical
  by_cases hdir : ∃ e ∈ K, e ⊆ A
  · obtain ⟨e,he,hea⟩ := hdir
    obtain ⟨a,b,hab,heab⟩ := Finset.card_eq_two.mp (h2 e he)
    left
    exact ⟨a,hea (by rw [heab]; simp),b,hea (by rw [heab]; simp),hab,
      (direct_singleton hc he hea).trans (congrArg singleton heab)⟩
  · have hout : ∀ e ∈ K, ∃ v ∈ e, v ∉ A := by
      intro e he
      by_contra h
      push_neg at h
      exact hdir ⟨e,he,h⟩
    exact Or.inr ⟨hout, SKGraphShapes.exists_path_or_cycle (usedGraph A K)
      (usedGraph_connected A K hne hc h2 hout) (usedGraph_degree_le_two A K h2 hd)⟩

end SpinGlass.SKPrimitiveCatalog
