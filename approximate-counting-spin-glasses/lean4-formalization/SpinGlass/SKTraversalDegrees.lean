import SpinGlass.SKTraversalStructure

/-! # Exact vertex degrees of simple path and cycle traversals -/
noncomputable section
namespace SpinGlass.SKTraversal
open Finset
variable {V : Type*} [DecidableEq V]

/-- Inserted edges increment the actual incidence count at each contained vertex. -/
theorem degree_insert {Γ : Finset (Finset V)} {e : Finset V} (he : e∉Γ) (v : V) :
    SpinGlass.Expansion.degree id (insert e Γ) v =
      SpinGlass.Expansion.degree id Γ v + if v∈e then 1 else 0 := by
  unfold SpinGlass.Expansion.degree
  simp only [id_eq]
  by_cases hv : v∈e
  · have hnot : e∉Γ.filter (fun e => v∈e) := fun h => he (Finset.mem_filter.mp h).1
    simp [Finset.filter_insert, hv, Finset.card_insert_of_notMem hnot]
  · simp [Finset.filter_insert, hv]

/-- The incidence count plus the two endpoint deficits is exactly two at every
listed vertex, including the single-vertex path case. -/
theorem pathEdges_degree_balance {l : List V} (hl : l.Nodup) (v : V) :
    SpinGlass.Expansion.degree id (pathEdges l) v +
      (if l.head?=some v then 1 else 0) + (if l.getLast?=some v then 1 else 0) =
      if v∈l then 2 else 0 := by
  induction l with
  | nil => simp [pathEdges, SpinGlass.Expansion.degree]
  | cons x l ih =>
    cases l with
    | nil =>
      by_cases h : v=x
      · subst v; simp [pathEdges, SpinGlass.Expansion.degree]
      · simp [pathEdges, SpinGlass.Expansion.degree, h, Ne.symm h]
    | cons y ys =>
      have ht := ih (List.nodup_cons.mp hl).2
      rw [pathEdges, degree_insert (not_mem_pathEdges (List.nodup_cons.mp hl).1 (by simp))]
      by_cases hv : v=x
      · subst v
        have hx : x∉y::ys := (List.nodup_cons.mp hl).1
        have hlast : (y::ys).getLast?≠some x := by
          rw [List.getLast?_eq_some_getLast (by simp)]
          intro h
          exact hx ((Option.some.inj h) ▸ List.getLast_mem (by simp))
        have hxy : y≠x := by intro h; subst y; simp at hx
        simp only [List.head?_cons, List.getLast?_cons_cons, Option.some.injEq,
          hxy, if_false, hlast, hx, Nat.add_zero] at ht
        simp [List.getLast?_cons_cons, hlast, ht]
      · by_cases hy : y=v
        · subst y
          simp only [List.head?_cons, Option.some.injEq, if_pos rfl,
            List.mem_cons_self, if_true] at ht
          simp only [Finset.mem_insert, Finset.mem_singleton, hv, or_true, if_true,
            List.head?_cons, Option.some.injEq, Ne.symm hv, if_false,
            List.getLast?_cons_cons, List.mem_cons, true_or, or_true, Nat.add_zero]
          omega
        · simp only [List.head?_cons, Option.some.injEq, hy, if_false, Nat.add_zero] at ht
          simpa only [Finset.mem_insert, Finset.mem_singleton, hv, Ne.symm hy,
            or_self, if_false, Nat.add_zero, List.head?_cons, Option.some.injEq,
            Ne.symm hv, List.getLast?_cons_cons, List.mem_cons, false_or] using ht

/-- The edge deleted at the initial root is absent from the remaining simple path. -/
theorem rooted_first_notin {root x y : V} {xs : List V}
    (hl : (x::y::xs).Nodup) (hr : root∉x::y::xs) :
    ({root,x}:Finset V)∉pathEdges ((x::y::xs)++[root]) := by
  rw [pathEdges_concat, Finset.mem_insert]
  rintro (he | he)
  · have hm : (x::y::xs).getLast (by simp)∈({root,x}:Finset V) := by rw [he]; simp
    have hor : (x::y::xs).getLast (by simp)=root ∨ (x::y::xs).getLast (by simp)=x := by
      simpa using hm
    rcases hor with h | h
    · exact hr (h ▸ List.getLast_mem (by simp))
    · exact head_ne_last hl h.symm
  · exact not_mem_pathEdges hr (by simp) he

/-- Every used vertex, including the branch root, has degree two in one return. -/
theorem rootedEdges_degree {root : V} {l : List V} (hl : l.Nodup) (hr : root∉l)
    (hlen : 2≤l.length) (v : V) :
    SpinGlass.Expansion.degree id (rootedEdges root l) v = if v=root ∨ v∈l then 2 else 0 := by
  obtain ⟨x,y,xs,rfl⟩ : ∃ x y xs, l=x::y::xs := by
    cases l with
    | nil => simp at hlen
    | cons x l => cases l with
      | nil => simp at hlen
      | cons y xs => exact ⟨x,y,xs,rfl⟩
  have ht := pathEdges_degree_balance (nodup_append_root hl hr) v
  change SpinGlass.Expansion.degree id (insert {root,x} (pathEdges ((x::y::xs)++[root]))) v = _
  rw [degree_insert (rooted_first_notin hl hr)]
  have hlast : ((x::y::xs)++[root]).getLast?=some root := by
    rw [List.getLast?_eq_some_getLast (by simp), List.getLast_concat]
  have hhead : ((x::y::xs)++[root]).head?=some x := rfl
  rw [hlast, hhead] at ht
  simp only [Option.some.injEq, List.mem_append, List.mem_singleton] at ht
  by_cases hvr : v=root
  · subst v
    have hxr : x≠root := by intro h; subst x; simp at hr
    simpa [hxr] using ht
  · by_cases hvx : v=x
    · subst v
      simpa [hvr, Ne.symm hvr] using ht
    · simpa only [Finset.mem_insert, Finset.mem_singleton, hvr, hvx, or_self,
        if_false, Nat.add_zero, Ne.symm hvx, Ne.symm hvr, false_or, or_false] using ht

/-- Outside simple cycles have degree exactly two at every used vertex. -/
theorem cycleEdges_degree {l : List V} (hl : l.Nodup) (hlen : 3≤l.length) (v : V) :
    SpinGlass.Expansion.degree id (cycleEdges l) v = if v∈l then 2 else 0 := by
  cases l with
  | nil => simp at hlen
  | cons root l =>
    simpa only [cycleEdges, List.mem_cons] using
      rootedEdges_degree (List.nodup_cons.mp hl).2 (List.nodup_cons.mp hl).1
        (by simpa using hlen) v

end SpinGlass.SKTraversal
