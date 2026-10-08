import SpinGlass.SKTraversalRooted

/-! # Exact rooted and unrooted cycle representation counts -/
noncomputable section
namespace SpinGlass.SKTraversal
open Finset
variable {V : Type*} [DecidableEq V]

/-- The actual finite fiber among all permutations of the interior vertices. -/
def rootedRepresentations (root : V) (l : List V) : Finset (List V) :=
  l.permutations.toFinset.filter (fun q => rootedEdges root q=rootedEdges root l)

theorem rootedRepresentations_eq {root : V} {l : List V}
    (hl : l.Nodup) (hr : root∉l) (hlen : 2≤l.length) :
    rootedRepresentations root l=rootedFiber root l := by
  ext q
  simp only [rootedRepresentations, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hperm, he⟩
    exact (mem_rootedFiber hl (hperm.nodup_iff.mpr hl) hr
      (fun h => hr (hperm.mem_iff.mp h)) hlen (by simpa [hperm.length_eq] using hlen)).mpr he
  · intro hq
    have hor : q=l ∨ q=l.reverse := by simpa [rootedFiber] using hq
    rcases hor with rfl | rfl
    · exact ⟨List.Perm.refl _, rfl⟩
    · exact ⟨List.reverse_perm _, rootedEdges_reverse root l⟩

theorem rootedRepresentations_card {root : V} {l : List V}
    (hl : l.Nodup) (hr : root∉l) (hlen : 2≤l.length) :
    (rootedRepresentations root l).card=2 := by
  rw [rootedRepresentations_eq hl hr hlen, rootedFiber_card hl hlen]

/-- Moving the first vertex to the end preserves the actual undirected cycle. -/
theorem cycleEdges_rotate_one (x : V) (l : List V) :
    cycleEdges (x::l)=cycleEdges (l++[x]) := by
  cases l with
  | nil => rfl
  | cons y ys =>
    change insert {x,y} (pathEdges (y::(ys++[x]))) =
      pathEdges (y::((ys++[x])++[y]))
    have h := pathEdges_concat (ys++[x]) y y
    have hlast : (y::(ys++[x])).getLast (by simp)=x := by
      simpa only [List.cons_append] using (List.getLast_concat (l:=y::ys) (a:=x))
    rw [hlast] at h
    simpa only [List.cons_append, List.append_assoc, List.singleton_append] using h.symm

/-- Every cut-and-rotate of the traversal preserves its edge set. -/
theorem cycleEdges_append_rotate (l q : List V) : cycleEdges (l++q)=cycleEdges (q++l) := by
  induction l generalizing q with
  | nil => simp
  | cons x l ih =>
    calc
      cycleEdges ((x::l)++q) = cycleEdges ((l++q)++[x]) := cycleEdges_rotate_one x (l++q)
      _ = cycleEdges (l++(q++[x])) := by rw [List.append_assoc]
      _ = cycleEdges ((q++[x])++l) := ih _
      _ = cycleEdges (q++(x::l)) := by simp only [List.append_assoc, List.singleton_append]

/-- Rotate at any chosen vertex, with both the permutation and edge equality proved. -/
theorem exists_cycle_root {l : List V} {root : V} (hr : root∈l) :
    ∃ q : List V, (root::q).Perm l ∧ cycleEdges (root::q)=cycleEdges l := by
  have hsplit : ∃ xs ys : List V, l=xs++(root::ys) := by
    induction l with
    | nil => simp at hr
    | cons x l ih =>
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨[],l,rfl⟩
      · obtain ⟨xs,ys,h⟩ := ih hr
        exact ⟨x::xs,ys,by simp [h]⟩
  obtain ⟨xs,ys,rfl⟩ := hsplit
  refine ⟨ys++xs, ?_, ?_⟩
  · exact List.perm_append_comm (l₁:=root::ys) (l₂:=xs)
  · exact cycleEdges_append_rotate (root::ys) xs

/-- The actual outside-cycle fiber, allowing every starting vertex and orientation. -/
def cycleRepresentations (l : List V) : Finset (List V) :=
  l.permutations.toFinset.filter (fun q => cycleEdges q=cycleEdges l)

/-- Changing a representative preserves the complete, explicitly enumerated fiber. -/
theorem cycleRepresentations_congr {l q : List V} (hperm : l.Perm q)
    (he : cycleEdges l=cycleEdges q) : cycleRepresentations l=cycleRepresentations q := by
  ext a
  simp only [cycleRepresentations, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hp,ha⟩; exact ⟨hp.trans hperm, ha.trans he⟩
  · rintro ⟨hp,ha⟩; exact ⟨hp.trans hperm.symm, ha.trans he.symm⟩

/-- The fiber at one root is exactly the actual two-orientation interior fiber. -/
theorem cycleRepresentations_root_filter (root : V) (l : List V) :
    (cycleRepresentations (root::l)).filter (fun q => q.head?=some root) =
      (rootedRepresentations root l).image (List.cons root) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hq,hh⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hq
    have hp := List.mem_permutations.mp (List.mem_toFinset.mp hp)
    cases q with
    | nil => simp at hh
    | cons a as =>
      have ha : a=root := by simpa using hh
      subst a
      apply Finset.mem_image.mpr
      refine ⟨as, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨by simpa using hp.cons_inv, he⟩
  · intro hq
    obtain ⟨as,ha,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp ha
    have hp := List.mem_permutations.mp (List.mem_toFinset.mp hp)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_,he⟩,rfl⟩
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr (List.Perm.cons root hp))

theorem cycleRepresentations_root_card {root : V} {l : List V}
    (hl : l.Nodup) (hr : root∉l) (hlen : 2≤l.length) :
    ((cycleRepresentations (root::l)).filter (fun q => q.head?=some root)).card=2 := by
  rw [cycleRepresentations_root_filter, Finset.card_image_of_injective _ List.cons_injective,
    rootedRepresentations_card hl hr hlen]

/-- Every root and each orientation is counted once: the exact factor `2 |S|`. -/
theorem cycleRepresentations_card {l : List V} (hl : l.Nodup) (hlen : 3≤l.length) :
    (cycleRepresentations l).card=2*l.length := by
  have hmap : Set.MapsTo List.head? (cycleRepresentations l : Set (List V))
      (l.toFinset.image some : Set (Option V)) := by
    intro q hq
    have hp := List.mem_permutations.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hq).1)
    cases q with
    | nil => have h := hp.length_eq; simp at h; omega
    | cons a as =>
      apply Finset.mem_image.mpr
      refine ⟨a, ?_, rfl⟩
      exact List.mem_toFinset.mpr (hp.mem_iff.mp (by simp))
  rw [Finset.card_eq_sum_card_fiberwise hmap, Finset.sum_image]
  · have hf : ∀ root∈l.toFinset,
        ((cycleRepresentations l).filter (fun q => q.head?=some root)).card=2 := by
      intro root hr
      obtain ⟨q,hp,he⟩ := exists_cycle_root (List.mem_toFinset.mp hr)
      have hn : (root::q).Nodup := hp.nodup_iff.mpr hl
      have hqen : 2≤q.length := by have h := hp.length_eq; simp at h; omega
      rw [← cycleRepresentations_congr hp he]
      exact cycleRepresentations_root_card (List.nodup_cons.mp hn).2
        (List.nodup_cons.mp hn).1 hqen
    rw [Finset.sum_congr rfl hf]
    simp [List.toFinset_card_of_nodup hl, Nat.mul_comm]
  · intro a ha b hb h
    exact Option.some.inj h

end SpinGlass.SKTraversal
