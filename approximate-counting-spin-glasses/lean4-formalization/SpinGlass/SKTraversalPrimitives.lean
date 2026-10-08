import SpinGlass.SKTraversalClosure
import SpinGlass.SKTraversalDegrees

/-! # Structural coordinates of the primitive path and cycle edge families -/
noncomputable section
namespace SpinGlass.SKTraversal
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem betweenEdges_support (a b : V) (l : List V) :
    SpinGlass.Hypergraph.support (betweenEdges a b l)=insert a (insert b l.toFinset) := by
  rw [betweenEdges, pathEdges_support (by simp)]
  ext v
  simp
  tauto

theorem betweenEdges_card {a b : V} {l : List V} (hab : a≠b)
    (hl : l.Nodup) (ha : a∉l) (hb : b∉l) :
    (betweenEdges a b l).card=l.length+1 := by
  rw [betweenEdges, pathEdges_card (between_list_nodup hab hl ha hb)]
  simp

theorem betweenEdges_uniform {a b : V} {l : List V} (hab : a≠b)
    (hl : l.Nodup) (ha : a∉l) (hb : b∉l) {e : Finset V} (he : e∈betweenEdges a b l) :
    e.card=2 := pathEdges_uniform (between_list_nodup hab hl ha hb) he

/-- A branch path has degree one at its distinct branch endpoints and degree two
at every interior vertex. This includes the empty-interior direct-edge case. -/
theorem betweenEdges_degree {a b : V} {l : List V} (hab : a≠b)
    (hl : l.Nodup) (ha : a∉l) (hb : b∉l) (v : V) :
    SpinGlass.Expansion.degree id (betweenEdges a b l) v =
      if v=a ∨ v=b then 1 else if v∈l then 2 else 0 := by
  have ht := pathEdges_degree_balance (between_list_nodup hab hl ha hb) v
  have hhead : (b::(l++[a])).head?=some b := rfl
  have hlast : (b::(l++[a])).getLast?=some a := by
    have h : ((b::l)++[a]).getLast?=some a := by
      rw [List.getLast?_eq_some_getLast (by simp), List.getLast_concat]
    simpa only [List.cons_append] using h
  rw [hhead, hlast] at ht
  simp only [Option.some.injEq, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at ht
  change SpinGlass.Expansion.degree id (pathEdges (b::(l++[a]))) v = _
  by_cases hva : v=a
  · subst v
    simp only [Ne.symm hab, if_false, if_pos rfl, Nat.add_zero, or_true, if_true] at ht
    simpa using ht
  · by_cases hvb : v=b
    · subst v
      simp only [if_pos rfl, hab, if_false, Nat.add_zero, true_or, if_true] at ht
      simpa using ht
    · simp only [hva,hvb,or_self,if_false]
      simpa only [Ne.symm hva, Ne.symm hvb, if_false, Nat.add_zero,
        hva,hvb,false_or,or_false] using ht

/-- Cycles satisfy the even-degree predicate used in the graphical expansion. -/
theorem rootedEdges_isEven {root : V} {l : List V}
    (hl : l.Nodup) (hr : root∉l) (hlen : 2≤l.length) :
    SpinGlass.Expansion.IsEven id (rootedEdges root l) := by
  intro v
  rw [rootedEdges_degree hl hr hlen]
  split_ifs <;> norm_num

theorem cycleEdges_isEven {l : List V} (hl : l.Nodup) (hlen : 3≤l.length) :
    SpinGlass.Expansion.IsEven id (cycleEdges l) := by
  intro v
  rw [cycleEdges_degree hl hlen]
  split_ifs <;> norm_num

end SpinGlass.SKTraversal
