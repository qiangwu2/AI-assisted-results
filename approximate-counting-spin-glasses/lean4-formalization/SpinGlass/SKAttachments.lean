import SpinGlass.SKOutsideClassification

/-!
# Exact numbers of branch attachments of outside vertices

Neighbor counts are preserved when passing to a connected component. The degree
two identity is then split between outside edges and edges to the branch set.
This identifies the two attachments of an isolated outside vertex, the single
attachment at a path endpoint, and the absence of attachments inside a path or
on an outside cycle.
-/

noncomputable section

namespace SpinGlass.SKAttachments

open SimpleGraph SKComponents SKOutsideClassification

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance (G : SimpleGraph V) : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

/-- Connected-component restriction is a bijection on each vertex's neighbors. -/
def componentNeighborEquiv (G : SimpleGraph V) (C : G.ConnectedComponent) (v : C) :
    C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val where
  toFun w := ⟨w.val.val, w.property⟩
  invFun w := ⟨⟨w.val, C.mem_supp_of_adj_mem_supp v.property w.property⟩, w.property⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

/-- The full outside-neighbor count is unchanged within its actual component. -/
theorem component_neighbor_card (G : SimpleGraph V) (C : G.ConnectedComponent) (v : C) :
    (C.toSimpleGraph.neighborSet v).ncard = (G.neighborSet v.val).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card',
    Set.toFinset_card, Set.toFinset_card]
  exact Fintype.card_congr (componentNeighborEquiv G C v)

/-- Neighbors in an induced complement correspond exactly to outside neighbors. -/
theorem outside_neighbor_card (G : SimpleGraph V) (A : Finset V) (v : {v : V // v ∉ A}) :
    ((G.induce {v | v ∉ A}).neighborSet v).ncard =
      ((G.neighborSet v.val).toFinset.filter (fun w => w ∉ A)).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw
    have ha : G.Adj v.val w.val := by
      simpa only [Set.mem_toFinset, mem_neighborSet, induce_adj] using hw
    exact Finset.mem_filter.mpr ⟨by simpa using ha, w.property⟩
  · intro w hw w' hw' heq
    exact Subtype.ext heq
  · intro w hw
    obtain ⟨ha, hwA⟩ := Finset.mem_filter.mp hw
    refine ⟨⟨w, hwA⟩, ?_, rfl⟩
    simpa only [Set.mem_toFinset, mem_neighborSet, induce_adj] using ha

/-- The branch vertices joined by actual selected edges to a given outside vertex. -/
def attachments (Γ : Finset (Finset V)) (A : Finset V) (v : V) : Finset V := by
  classical
  exact ((graph Γ).neighborSet v).toFinset.filter (fun w => w ∈ A)

/-- Every original incident edge is either outside or is a branch attachment. -/
theorem outside_add_attachments (Γ : Finset (Finset V)) (h2 : ∀ e ∈ Γ, e.card = 2)
    (A : Finset V) (v : {v : V // v ∉ A}) :
    (((graph Γ).induce {v | v ∉ A}).neighborSet v).ncard +
      (attachments Γ A v.val).card = Expansion.degree id Γ v.val := by
  classical
  rw [outside_neighbor_card, attachments, ← neighbor_card_eq_degree Γ h2,
    Set.ncard_eq_toFinset_card']
  rw [Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- The full degree-two budget at a used outside vertex splits exactly. -/
theorem outside_add_attachments_eq_two (Γ : Finset (Finset V))
    (h2 : ∀ e ∈ Γ, e.card = 2) (heven : Expansion.IsEven id Γ)
    (v : {v : V // v ∉ branchVertices id Γ}) (e : Γ) (hev : v.val ∈ e.val) :
    ((outsideGraph Γ).neighborSet v).ncard +
      (attachments Γ (branchVertices id Γ) v.val).card = 2 := by
  exact (outside_add_attachments Γ h2 (branchVertices id Γ) v).trans
    (outside_degree_two id Γ heven v.val v.property e hev)

/-- The same exact budget holds in the actual outside connected component. -/
theorem component_add_attachments_eq_two (Γ : Finset (Finset V))
    (h2 : ∀ e ∈ Γ, e.card = 2) (heven : Expansion.IsEven id Γ)
    (C : (outsideGraph Γ).ConnectedComponent) (v : C) (e : Γ)
    (hev : v.val.val ∈ e.val) :
    (C.toSimpleGraph.neighborSet v).ncard +
      (attachments Γ (branchVertices id Γ) v.val.val).card = 2 := by
  rw [component_neighbor_card]
  exact outside_add_attachments_eq_two Γ h2 heven v.val e hev

/-- An isolated used outside vertex has precisely two distinct branch neighbors. -/
theorem isolated_two_attachments (Γ : Finset (Finset V))
    (h2 : ∀ e ∈ Γ, e.card = 2) (heven : Expansion.IsEven id Γ)
    (v : {v : V // v ∉ branchVertices id Γ}) (e : Γ) (hev : v.val ∈ e.val)
    (hisolated : ((outsideGraph Γ).neighborSet v).ncard = 0) :
    ∃ a b, a ≠ b ∧ attachments Γ (branchVertices id Γ) v.val = {a, b} := by
  have h := outside_add_attachments_eq_two Γ h2 heven v e hev
  rw [hisolated, Nat.zero_add] at h
  exact Finset.card_eq_two.mp h

/-- Outside degree one leaves exactly one branch attachment. -/
theorem endpoint_one_attachment (Γ : Finset (Finset V))
    (h2 : ∀ e ∈ Γ, e.card = 2) (heven : Expansion.IsEven id Γ)
    (v : {v : V // v ∉ branchVertices id Γ}) (e : Γ) (hev : v.val ∈ e.val)
    (hendpoint : ((outsideGraph Γ).neighborSet v).ncard = 1) :
    (attachments Γ (branchVertices id Γ) v.val).card = 1 := by
  have h := outside_add_attachments_eq_two Γ h2 heven v e hev
  omega

/-- Outside degree two consumes all incident edges and permits no branch attachment. -/
theorem degree_two_no_attachment (Γ : Finset (Finset V))
    (h2 : ∀ e ∈ Γ, e.card = 2) (heven : Expansion.IsEven id Γ)
    (v : {v : V // v ∉ branchVertices id Γ}) (e : Γ) (hev : v.val ∈ e.val)
    (hinternal : ((outsideGraph Γ).neighborSet v).ncard = 2) :
    attachments Γ (branchVertices id Γ) v.val = ∅ := by
  have h := outside_add_attachments_eq_two Γ h2 heven v e hev
  apply Finset.card_eq_zero.mp
  omega

end SpinGlass.SKAttachments
