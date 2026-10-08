import SpinGlass.SKPrimitiveCatalogWalk

/-! # Converse connectivity of each concrete traversal primitive -/
noncomputable section
namespace SpinGlass.SKPrimitiveCatalogWalk
open Finset SpinGlass.SKTraversal SpinGlass.SKBlockPartition SpinGlass.SKComponents
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem connected_singleton (A : Finset V) (e : Finset V) :
    Connected id A ({e}:Finset (Finset V)) := by
  intro f g
  have hfg : f=g := Subtype.ext ((Finset.mem_singleton.mp f.property).trans
    (Finset.mem_singleton.mp g.property).symm)
  subst g
  exact related_refl _ _ _ _

/-- Adding an edge sharing an outside vertex preserves the concrete edge relation. -/
theorem connected_insert (A : Finset V) {H : Finset (Finset V)} {e f : Finset V}
    (hc : Connected id A H) (hf : f∈H) {v : V} (hv : v∉A) (hve : v∈e) (hvf : v∈f) :
    Connected id A (insert e H) := by
  have hsub : H⊆insert e H := Finset.subset_insert _ _
  let anchor : ↥(insert e H) := ⟨f,Finset.mem_insert_of_mem hf⟩
  have hroot : ∀ g : ↥(insert e H), Related id A (insert e H) g anchor := by
    rintro ⟨g,hg⟩
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact Relation.EqvGen.rel _ _ ⟨v,hv,hve,hvf⟩
    · exact related_mono id A hsub (hc ⟨g,hg⟩ ⟨f,hf⟩)
  intro g h
  exact related_trans id A _ (hroot g) (related_symm id A _ (hroot h))

/-- The edge relation connects an entire path through its outside interior vertices.
No branch-endpoint distinctness or simplicity hypothesis is needed for this fact. -/
theorem betweenEdges_connected (A : Finset V) (a b : V) (l : List V)
    (hout : ∀ v∈l, v∉A) : Connected id A (betweenEdges a b l) := by
  induction l generalizing b with
  | nil => simpa [betweenEdges, pathEdges] using connected_singleton A ({b,a}:Finset V)
  | cons x xs ih =>
    change Connected id A (insert {b,x} (betweenEdges a x xs))
    have hc := ih x (fun v hv => hout v (List.mem_cons_of_mem x hv))
    have hfirst : ∃ f∈betweenEdges a x xs, x∈f := by
      cases xs with
      | nil => exact ⟨{x,a},by simp [betweenEdges,pathEdges],by simp⟩
      | cons y ys => exact ⟨{x,y},by simp [betweenEdges,pathEdges],by simp⟩
    obtain ⟨f,hf,hxf⟩ := hfirst
    exact connected_insert A hc hf (hout x (by simp)) (by simp) hxf

theorem rootedEdges_connected (A : Finset V) (a : V) (l : List V)
    (hout : ∀ v∈l, v∉A) : Connected id A (rootedEdges a l) :=
  betweenEdges_connected A a a l hout

theorem cycleEdges_connected (A : Finset V) (l : List V)
    (hout : ∀ v∈l, v∉A) : Connected id A (cycleEdges l) := by
  cases l with
  | nil =>
    intro e f
    have h : e.val∈(∅ : Finset (Finset V)) := e.property
    exact False.elim (Finset.notMem_empty _ h)
  | cons root l =>
    exact rootedEdges_connected A root l (fun v hv => hout v (List.mem_cons_of_mem root hv))

end SpinGlass.SKPrimitiveCatalogWalk
