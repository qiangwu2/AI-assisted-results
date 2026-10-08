import SpinGlass.SKTraversalPath

/-! # Exact two-orientation fibers of an undirected rooted cycle -/
noncomputable section
namespace SpinGlass.SKTraversal
open Finset
variable {V : Type*} [DecidableEq V]

/-- The root has just the two endpoint attachments of the interior path. -/
theorem rootedEdges_decompose (root x : V) (xs : List V) :
    rootedEdges root (x::xs) = insert {root,x}
      (insert {(x::xs).getLast (by simp),root} (pathEdges (x::xs))) := by
  simp only [rootedEdges, List.cons_append, pathEdges]
  rw [← pathEdges_concat]
  rfl

/-- No other neighbor of the root is possible in an interior-simple traversal. -/
theorem rooted_neighbor {root x z : V} {xs : List V} (hr : root∉x::xs)
    (he : ({root,z}:Finset V)∈rootedEdges root (x::xs)) :
    z=x ∨ z=(x::xs).getLast (by simp) := by
  rw [rootedEdges_decompose, Finset.mem_insert, Finset.mem_insert] at he
  rcases he with he | he | he
  · left
    have hm : x∈({root,z}:Finset V) := by rw [he]; simp
    have hxr : x≠root := by intro h; subst x; simp at hr
    have hor : x=root ∨ x=z := by simpa using hm
    exact hor.elim (fun h => False.elim (hxr h)) Eq.symm
  · right
    have hm : (x::xs).getLast (by simp)∈({root,z}:Finset V) := by rw [he]; simp
    have hnr : (x::xs).getLast (by simp)≠root := by
      intro h; exact hr (h ▸ List.getLast_mem (by simp))
    have hor : (x::xs).getLast (by simp)=root ∨ (x::xs).getLast (by simp)=z := by
      simpa using hm
    exact hor.elim (fun h => False.elim (hnr h)) Eq.symm
  · exact False.elim (not_mem_pathEdges hr (by simp) he)

theorem head_ne_last {x y : V} {xs : List V} (hn : (x::y::xs).Nodup) :
    x≠(x::y::xs).getLast (by simp) := by
  intro h
  apply (List.nodup_cons.mp hn).1
  rw [h, List.getLast_cons_cons]
  exact List.getLast_mem (by simp)

/-- Deleting the initial root edge leaves the unique simple path back to root. -/
theorem rooted_erase_first {root x y : V} {xs : List V}
    (hn : (x::y::xs).Nodup) (hr : root∉x::y::xs) :
    (rootedEdges root (x::y::xs)).erase {root,x} = pathEdges ((x::y::xs)++[root]) := by
  change (insert {root,x} (pathEdges ((x::y::xs)++[root]))).erase {root,x} = _
  apply Finset.erase_insert
  rw [pathEdges_concat, Finset.mem_insert]
  rintro (he | he)
  · have hm : (x::y::xs).getLast (by simp)∈({root,x}:Finset V) := by rw [he]; simp
    have hor : (x::y::xs).getLast (by simp)=root ∨ (x::y::xs).getLast (by simp)=x := by
      simpa using hm
    rcases hor with h | h
    · exact hr (h ▸ List.getLast_mem (by simp))
    · exact head_ne_last hn h.symm
  · exact not_mem_pathEdges hr (by simp) he

theorem nodup_append_root {root : V} {l : List V} (hn : l.Nodup) (hr : root∉l) :
    (l++[root]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hn, by simp, ?_⟩
  intro a ha b hb
  have hb' : b=root := by simpa using hb
  subst b
  intro h; exact hr (h ▸ ha)

/-- A rooted undirected cycle is determined by the first neighbor after the root. -/
theorem rootedEdges_head_injective {root : V} {l q : List V}
    (hl : l.Nodup) (hq : q.Nodup) (hrl : root∉l) (hrq : root∉q)
    (hlen : 2≤l.length) (hqen : 2≤q.length)
    (hh : l.head?=q.head?) (he : rootedEdges root l=rootedEdges root q) : l=q := by
  obtain ⟨x,y,xs,rfl⟩ : ∃ x y xs, l=x::y::xs := by
    cases l with
    | nil => simp at hlen
    | cons x l => cases l with
      | nil => simp at hlen
      | cons y xs => exact ⟨x,y,xs,rfl⟩
  obtain ⟨a,b,bs,rfl⟩ : ∃ a b bs, q=a::b::bs := by
    cases q with
    | nil => simp at hqen
    | cons a q => cases q with
      | nil => simp at hqen
      | cons b bs => exact ⟨a,b,bs,rfl⟩
  have hax : x=a := by simpa using hh
  subst a
  have hpath : pathEdges ((x::y::xs)++[root])=pathEdges ((x::b::bs)++[root]) := by
    rw [← rooted_erase_first hl hrl, he, rooted_erase_first hq hrq]
  exact List.append_cancel_right (pathEdges_head_injective
    (nodup_append_root hl hrl) (nodup_append_root hq hrq) rfl hpath)

/-- Every representation is one of the two orientations; this is reconstruction,
not a definition of equivalence or an assumed symmetry quotient. -/
theorem rootedEdges_fiber {root : V} {l q : List V}
    (hl : l.Nodup) (hq : q.Nodup) (hrl : root∉l) (hrq : root∉q)
    (hlen : 2≤l.length) (hqen : 2≤q.length) :
    rootedEdges root l=rootedEdges root q ↔ q=l ∨ q=l.reverse := by
  constructor
  · intro he
    obtain ⟨x,xs,rfl⟩ : ∃ x xs, l=x::xs := List.exists_cons_of_ne_nil (by intro h; simp [h] at hlen)
    obtain ⟨a,as,rfl⟩ : ∃ a as, q=a::as := List.exists_cons_of_ne_nil (by intro h; simp [h] at hqen)
    have ham : ({root,a}:Finset V)∈rootedEdges root (x::xs) := by
      rw [he, rootedEdges_decompose]
      simp
    rcases rooted_neighbor hrl ham with h | h
    · left
      exact (rootedEdges_head_injective hl hq hrl hrq hlen hqen (by simp [h]) he).symm
    · right
      have hhead : (x::xs).reverse.head? = (a::as).head? := by
        rw [List.head?_reverse, List.getLast?_eq_some_getLast (by simp)]
        simp [h]
      have hrev : rootedEdges root (x::xs).reverse=rootedEdges root (a::as) := by
        simpa only [rootedEdges_reverse] using he
      exact (rootedEdges_head_injective (List.nodup_reverse.mpr hl) hq
        (by simpa only [List.mem_reverse] using hrl) hrq
        (by simpa only [List.length_reverse] using hlen) hqen hhead hrev).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (rootedEdges_reverse root l).symm

/-- The two orientations are distinct as soon as the interior has two vertices. -/
theorem reverse_ne_of_nodup {l : List V} (hn : l.Nodup) (hlen : 2≤l.length) :
    l.reverse≠l := by
  obtain ⟨x,y,xs,rfl⟩ : ∃ x y xs, l=x::y::xs := by
    cases l with
    | nil => simp at hlen
    | cons x l => cases l with
      | nil => simp at hlen
      | cons y xs => exact ⟨x,y,xs,rfl⟩
  intro he
  have hh := congrArg List.head? he
  rw [List.head?_reverse, List.getLast?_eq_some_getLast (by simp)] at hh
  exact head_ne_last hn (Option.some.inj hh).symm

/-- Exact finite fiber, expressed without any selection of an orientation. -/
def rootedFiber (root : V) (l : List V) : Finset (List V) := {l,l.reverse}

theorem mem_rootedFiber {root : V} {l q : List V}
    (hl : l.Nodup) (hq : q.Nodup) (hrl : root∉l) (hrq : root∉q)
    (hlen : 2≤l.length) (hqen : 2≤q.length) :
    q∈rootedFiber root l ↔ rootedEdges root q=rootedEdges root l := by
  simp only [rootedFiber, Finset.mem_insert, Finset.mem_singleton]
  exact (rootedEdges_fiber hl hq hrl hrq hlen hqen).symm.trans eq_comm

theorem rootedFiber_card {root : V} {l : List V} (hn : l.Nodup) (hlen : 2≤l.length) :
    (rootedFiber root l).card=2 := by
  simp [rootedFiber, Finset.card_pair (reverse_ne_of_nodup hn hlen).symm]

end SpinGlass.SKTraversal
