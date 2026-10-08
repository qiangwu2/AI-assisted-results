import SpinGlass.SKTraversalWeights
import SpinGlass.Support

/-! # Supports and cardinalities recovered from actual traversal edge sets -/
noncomputable section
namespace SpinGlass.SKTraversal
open Finset
variable {V : Type*} [DecidableEq V]

/-- A path with at least one edge uses every and only its listed vertices. -/
theorem pathEdges_support {l : List V} (hlen : 2≤l.length) :
    SpinGlass.Hypergraph.support (pathEdges l)=l.toFinset := by
  induction l with
  | nil => simp at hlen
  | cons x l ih =>
    cases l with
    | nil => simp at hlen
    | cons y l =>
      cases l with
      | nil => simp [pathEdges, SpinGlass.Hypergraph.support]
      | cons z zs =>
        rw [pathEdges, SpinGlass.Hypergraph.support, Finset.biUnion_insert]
        change ({x,y}:Finset V) ∪ SpinGlass.Hypergraph.support (pathEdges (y::z::zs)) = _
        rw [ih (by simp)]
        ext v
        simp
        tauto

@[simp] theorem rootedEdges_support (root : V) (l : List V) :
    SpinGlass.Hypergraph.support (rootedEdges root l)=insert root l.toFinset := by
  rw [rootedEdges, pathEdges_support (by simp)]
  ext v
  simp

@[simp] theorem cycleEdges_support (l : List V) :
    SpinGlass.Hypergraph.support (cycleEdges l)=l.toFinset := by
  cases l with
  | nil => simp [cycleEdges, SpinGlass.Hypergraph.support]
  | cons x xs => simpa only [cycleEdges, List.toFinset_cons] using rootedEdges_support x xs

/-- An edge-set equality for simple cycle traversals already forces equal vertex sets. -/
theorem cycleEdges_perm {l q : List V} (hl : l.Nodup) (hq : q.Nodup)
    (he : cycleEdges l=cycleEdges q) : l.Perm q := by
  apply List.perm_of_nodup_nodup_toFinset_eq hl hq
  rw [← cycleEdges_support l, he, cycleEdges_support]

/-- The permutation-filter representation is the entire fiber among all simple lists. -/
theorem mem_cycleRepresentations_iff {l q : List V} (hl : l.Nodup) :
    q∈cycleRepresentations l ↔ q.Nodup ∧ cycleEdges q=cycleEdges l := by
  simp only [cycleRepresentations, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hp,he⟩; exact ⟨hp.nodup_iff.mpr hl,he⟩
  · rintro ⟨hq,he⟩; exact ⟨cycleEdges_perm hq hl he,he⟩

theorem rootedEdges_perm {root : V} {l q : List V} (hl : l.Nodup) (hq : q.Nodup)
    (hrl : root∉l) (hrq : root∉q) (he : rootedEdges root l=rootedEdges root q) : l.Perm q := by
  apply List.perm_of_nodup_nodup_toFinset_eq hl hq
  have hs := congrArg SpinGlass.Hypergraph.support he
  rw [rootedEdges_support, rootedEdges_support] at hs
  have ht := congrArg (fun s : Finset V => s.erase root) hs
  have hrl' : root∉l.toFinset := by simpa using hrl
  have hrq' : root∉q.toFinset := by simpa using hrq
  rw [Finset.erase_insert hrl', Finset.erase_insert hrq'] at ht
  exact ht

/-- Rooted representation completeness needs no prior permutation hypothesis. -/
theorem mem_rootedRepresentations_iff {root : V} {l q : List V}
    (hl : l.Nodup) (hrl : root∉l) :
    q∈rootedRepresentations root l ↔ q.Nodup ∧ root∉q ∧ rootedEdges root q=rootedEdges root l := by
  simp only [rootedRepresentations, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hp,he⟩
    exact ⟨hp.nodup_iff.mpr hl, fun h => hrl (hp.mem_iff.mp h),he⟩
  · rintro ⟨hq,hrq,he⟩
    exact ⟨rootedEdges_perm hq hl hrq hrl he,he⟩

/-- A simple rooted return has one more edge than interior vertices. -/
theorem rootedEdges_card {root : V} {l : List V}
    (hl : l.Nodup) (hr : root∉l) (hlen : 2≤l.length) :
    (rootedEdges root l).card=l.length+1 := by
  obtain ⟨x,y,xs,rfl⟩ : ∃ x y xs, l=x::y::xs := by
    cases l with
    | nil => simp at hlen
    | cons x l => cases l with
      | nil => simp at hlen
      | cons y xs => exact ⟨x,y,xs,rfl⟩
  have hm : ({root,x}:Finset V)∈rootedEdges root (x::y::xs) := by
    rw [rootedEdges_decompose]; simp
  have h := Finset.card_erase_add_one hm
  rw [rooted_erase_first hl hr, pathEdges_card (nodup_append_root hl hr)] at h
  simpa using h.symm

/-- A simple outside cycle has exactly one edge per listed vertex. -/
theorem cycleEdges_card {l : List V} (hl : l.Nodup) (hlen : 3≤l.length) :
    (cycleEdges l).card=l.length := by
  cases l with
  | nil => simp at hlen
  | cons root l =>
    exact rootedEdges_card (List.nodup_cons.mp hl).2 (List.nodup_cons.mp hl).1
      (by simpa using hlen)

/-- Every consecutive pair of a simple list is a genuine two-vertex edge. -/
theorem pathEdges_uniform {l : List V} (hl : l.Nodup) {e : Finset V}
    (he : e∈pathEdges l) : e.card=2 := by
  induction l with
  | nil => simp [pathEdges] at he
  | cons x l ih =>
    cases l with
    | nil => simp [pathEdges] at he
    | cons y l =>
      rw [pathEdges, Finset.mem_insert] at he
      rcases he with rfl | he
      · apply Finset.card_pair
        intro h
        exact (List.nodup_cons.mp hl).1 (by simp [h])
      · exact ih (List.nodup_cons.mp hl).2 he

/-- Returning cycles have no diagonal edge, including at either root attachment. -/
theorem rootedEdges_uniform {root : V} {l : List V} (hl : l.Nodup)
    (hr : root∉l) (hlen : 2≤l.length) {e : Finset V} (he : e∈rootedEdges root l) : e.card=2 := by
  obtain ⟨x,xs,rfl⟩ : ∃ x xs, l=x::xs := List.exists_cons_of_ne_nil (by intro h; simp [h] at hlen)
  change e∈insert {root,x} (pathEdges ((x::xs)++[root])) at he
  rcases Finset.mem_insert.mp he with rfl | he
  · apply Finset.card_pair
    intro h; subst root; simp at hr
  · exact pathEdges_uniform (nodup_append_root hl hr) he

theorem cycleEdges_uniform {l : List V} (hl : l.Nodup) (hlen : 3≤l.length)
    {e : Finset V} (he : e∈cycleEdges l) : e.card=2 := by
  cases l with
  | nil => simp at hlen
  | cons root l =>
    exact rootedEdges_uniform (List.nodup_cons.mp hl).2
      (List.nodup_cons.mp hl).1 (by simpa using hlen) he

end SpinGlass.SKTraversal
