import SpinGlass.SKTraversalCycles

/-! # Exact signed weights and cycle normalization of the chain recurrences -/
noncomputable section
namespace SpinGlass.SKTraversal
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The chain recurrence multiplies precisely the distinct consecutive edge weights. -/
theorem chainWeight_eq_product (f : Finset V → ℝ) {l : List V}
    (hn : l.Nodup) (hne : l≠[]) :
    SpinGlass.ColorPath.weight (fun _ => 1) (fun x y => f {x,y}) l =
      ∏ e∈pathEdges l, f e := by
  induction l with
  | nil => contradiction
  | cons x l ih =>
    cases l with
    | nil => simp [SpinGlass.ColorPath.weight, pathEdges]
    | cons y l =>
      rw [SpinGlass.ColorPath.weight, ih (List.nodup_cons.mp hn).2 (by simp),
        pathEdges, Finset.prod_insert (not_mem_pathEdges (List.nodup_cons.mp hn).1 (by simp))]
      rw [Finset.pair_comm y x, mul_comm]

/-- Recurrence (66), including the first branch edge and the final return edge. -/
def returnWeight (f : Finset V → ℝ) (root : V) (l : List V) : ℝ :=
  SpinGlass.ColorPath.weight (fun x => f {root,x}) (fun x y => f {x,y}) l *
    l.head?.elim 0 (fun x => f {x,root})

/-- The returning-chain weight is exactly the corresponding unordered edge product. -/
theorem returnWeight_eq_product (f : Finset V → ℝ) {root : V} {l : List V}
    (hn : l.Nodup) (hr : root∉l) (hlen : 2≤l.length) :
    returnWeight f root l = ∏ e∈rootedEdges root l, f e := by
  obtain ⟨x,y,xs,rfl⟩ : ∃ x y xs, l=x::y::xs := by
    cases l with
    | nil => simp at hlen
    | cons x l => cases l with
      | nil => simp at hlen
      | cons y xs => exact ⟨x,y,xs,rfl⟩
  have hm : ({root,x}:Finset V)∈rootedEdges root (x::y::xs) := by
    rw [rootedEdges_decompose]; simp
  rw [returnWeight, SpinGlass.ColorCycleChain.weight_factor_start_last,
    chainWeight_eq_product f hn (by simp),
    List.getLast?_eq_some_getLast (l:=x::y::xs) (by simp)]
  simp only [Option.elim_some, List.head?_cons]
  rw [← Finset.mul_prod_erase _ f hm, rooted_erase_first hn hr, pathEdges_concat,
    Finset.prod_insert (not_mem_pathEdges hr (by simp))]
  rw [Finset.pair_comm ((x::y::xs).getLast (by simp)) root, Finset.pair_comm x root]
  ring

/-- A complete outside-cycle chain closed by its final edge. -/
def cycleWeight (f : Finset V → ℝ) (l : List V) : ℝ :=
  SpinGlass.ColorPath.weight (fun _ => 1) (fun x y => f {x,y}) l *
    (l.head?.bind (fun x => l.getLast?.map (fun y => f {x,y}))).getD 0

theorem cycle_closing_notin {root x y : V} {xs : List V}
    (hn : (root::x::y::xs).Nodup) :
    ({root,(root::x::y::xs).getLast (by simp)}:Finset V)∉pathEdges (root::x::y::xs) := by
  intro he
  have h := head_pair_of_mem hn he
  exact head_ne_last (List.nodup_cons.mp hn).2 (by simpa only [List.getLast_cons_cons] using h.symm)

/-- Recurrence (69)'s closed-chain weight is exactly the cycle edge product. -/
theorem cycleWeight_eq_product (f : Finset V → ℝ) {l : List V}
    (hn : l.Nodup) (hlen : 3≤l.length) :
    cycleWeight f l = ∏ e∈cycleEdges l, f e := by
  obtain ⟨root,x,y,xs,rfl⟩ : ∃ root x y xs, l=root::x::y::xs := by
    cases l with
    | nil => simp at hlen
    | cons root l => cases l with
      | nil => simp at hlen
      | cons x l => cases l with
        | nil => simp at hlen
        | cons y xs => exact ⟨root,x,y,xs,rfl⟩
  rw [cycleWeight, chainWeight_eq_product f hn (by simp)]
  simp only [List.head?_cons, Option.bind_some, List.getLast?_eq_some_getLast (l:=root::x::y::xs) (by simp),
    Option.map_some, Option.getD_some]
  change _ = ∏ e∈pathEdges ((root::x::y::xs)++[root]), f e
  rw [pathEdges_concat, Finset.pair_comm _ root,
    Finset.prod_insert (cycle_closing_notin hn)]
  ring

/-- Both orientations have the same signed product, even for negative weights. -/
theorem rootedRepresentations_weight_sum (f : Finset V → ℝ) {root : V} {l : List V}
    (hl : l.Nodup) (hr : root∉l) (hlen : 2≤l.length) :
    (∑ q∈rootedRepresentations root l, returnWeight f root q) =
      2 * ∏ e∈rootedEdges root l, f e := by
  have hf : ∀ q∈rootedRepresentations root l,
      returnWeight f root q=∏ e∈rootedEdges root l, f e := by
    intro q hq
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hq
    have hp := List.mem_permutations.mp (List.mem_toFinset.mp hp)
    rw [returnWeight_eq_product f (hp.nodup_iff.mpr hl)
      (fun h => hr (hp.mem_iff.mp h)) (by simpa [hp.length_eq] using hlen), he]
  rw [Finset.sum_congr rfl hf, Finset.sum_const, rootedRepresentations_card hl hr hlen]
  simp

/-- The coefficient one half in (66) removes exactly the orientation multiplicity. -/
theorem rooted_normalization (f : Finset V → ℝ) {root : V} {l : List V}
    (hl : l.Nodup) (hr : root∉l) (hlen : 2≤l.length) :
    (∑ q∈rootedRepresentations root l, returnWeight f root q) / 2 =
      ∏ e∈rootedEdges root l, f e := by
  rw [rootedRepresentations_weight_sum f hl hr hlen]
  ring

/-- Every root and orientation contributes the same signed edge product. -/
theorem cycleRepresentations_weight_sum (f : Finset V → ℝ) {l : List V}
    (hl : l.Nodup) (hlen : 3≤l.length) :
    (∑ q∈cycleRepresentations l, cycleWeight f q) =
      (2*l.length:ℝ) * ∏ e∈cycleEdges l, f e := by
  have hf : ∀ q∈cycleRepresentations l,
      cycleWeight f q=∏ e∈cycleEdges l, f e := by
    intro q hq
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hq
    have hp := List.mem_permutations.mp (List.mem_toFinset.mp hp)
    rw [cycleWeight_eq_product f (hp.nodup_iff.mpr hl)
      (by simpa [hp.length_eq] using hlen), he]
  rw [Finset.sum_congr rfl hf, Finset.sum_const, cycleRepresentations_card hl hlen]
  simp

/-- The exact coefficient in (69) is one over twice the number of used colors. -/
theorem cycle_normalization (f : Finset V → ℝ) {l : List V}
    (hl : l.Nodup) (hlen : 3≤l.length) :
    (∑ q∈cycleRepresentations l, cycleWeight f q) / (2*l.length:ℝ) =
      ∏ e∈cycleEdges l, f e := by
  rw [cycleRepresentations_weight_sum f hl hlen]
  have hden : (2*l.length:ℝ)≠0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
  exact mul_div_cancel_left₀ _ hden

end SpinGlass.SKTraversal
