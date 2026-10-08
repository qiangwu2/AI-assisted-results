import SpinGlass.SKTraversalStructure

/-! # Summing each signed primitive graph once by its proven traversal fibers -/
noncomputable section
namespace SpinGlass.SKTraversal
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The representation set must contain all permutations that preserve its vertices.
Colorful chain sets satisfy this because colors do not depend on traversal order. -/
def PermutationClosed (F : Finset (List V)) : Prop :=
  ∀ l∈F, ∀ q, q.Perm l → q∈F

theorem rooted_filter_eq_representations (F : Finset (List V))
    (hclosed : PermutationClosed F) (hn : ∀ l∈F, l.Nodup)
    {root : V} (hr : ∀ l∈F, root∉l) {l : List V} (hl : l∈F) :
    F.filter (fun q => rootedEdges root q=rootedEdges root l)=rootedRepresentations root l := by
  ext q
  rw [Finset.mem_filter, mem_rootedRepresentations_iff (hn l hl) (hr l hl)]
  constructor
  · rintro ⟨hq,he⟩; exact ⟨hn q hq,hr q hq,he⟩
  · rintro ⟨hq,hrq,he⟩
    exact ⟨hclosed l hl q (rootedEdges_perm hq (hn l hl) hrq (hr l hl) he),he⟩

theorem cycle_filter_eq_representations (F : Finset (List V))
    (hclosed : PermutationClosed F) (hn : ∀ l∈F, l.Nodup) {l : List V} (hl : l∈F) :
    F.filter (fun q => cycleEdges q=cycleEdges l)=cycleRepresentations l := by
  ext q
  rw [Finset.mem_filter, mem_cycleRepresentations_iff (hn l hl)]
  constructor
  · rintro ⟨hq,he⟩; exact ⟨hn q hq,he⟩
  · rintro ⟨hq,he⟩
    exact ⟨hclosed l hl q (cycleEdges_perm hq (hn l hl) he),he⟩

/-- The return-chain closure divided by two sums precisely its graph image. -/
theorem return_sum_normalized (f : Finset V → ℝ) (F : Finset (List V))
    (hclosed : PermutationClosed F) (hn : ∀ l∈F, l.Nodup)
    {root : V} (hr : ∀ l∈F, root∉l) (hlen : ∀ l∈F, 2≤l.length) :
    (2:ℝ)⁻¹ * (∑ l∈F, returnWeight f root l) =
      ∑ Γ∈F.image (rootedEdges root), ∏ e∈Γ, f e := by
  have hm : Set.MapsTo (rootedEdges root) (F : Set (List V))
      (F.image (rootedEdges root) : Set (Finset (Finset V))) :=
    fun l hl => Finset.mem_image.mpr ⟨l,hl,rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  have hf : ∀ Γ∈F.image (rootedEdges root),
      (∑ l∈F.filter (fun l => rootedEdges root l=Γ), returnWeight f root l) =
        2*∏ e∈Γ, f e := by
    intro Γ hΓ
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
    rw [rooted_filter_eq_representations F hclosed hn hr hl]
    exact rootedRepresentations_weight_sum f (hn l hl) (hr l hl) (hlen l hl)
  rw [Finset.sum_congr rfl hf, ← Finset.mul_sum]
  ring

/-- The outside-cycle closure divided by `2 n` sums precisely its graph image. -/
theorem cycle_sum_normalized (f : Finset V → ℝ) (F : Finset (List V))
    (hclosed : PermutationClosed F) (hn : ∀ l∈F, l.Nodup)
    {n : ℕ} (hn3 : 3≤n) (hlen : ∀ l∈F, l.length=n) :
    (2*n:ℝ)⁻¹ * (∑ l∈F, cycleWeight f l) =
      ∑ Γ∈F.image cycleEdges, ∏ e∈Γ, f e := by
  have hm : Set.MapsTo cycleEdges (F : Set (List V))
      (F.image cycleEdges : Set (Finset (Finset V))) :=
    fun l hl => Finset.mem_image.mpr ⟨l,hl,rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  have hf : ∀ Γ∈F.image cycleEdges,
      (∑ l∈F.filter (fun l => cycleEdges l=Γ), cycleWeight f l) =
        (2*n:ℝ)*∏ e∈Γ, f e := by
    intro Γ hΓ
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
    rw [cycle_filter_eq_representations F hclosed hn hl,
      cycleRepresentations_weight_sum f (hn l hl) (by simpa [hlen l hl] using hn3), hlen l hl]
  rw [Finset.sum_congr rfl hf, ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))), one_mul]

/-- Undirected paths from the starting branch a to finishing branch b. Vertex
lists use the same reverse order as the dynamic-programming recurrence. -/
def betweenEdges (a b : V) (l : List V) : Finset (Finset V) := pathEdges (b::(l++[a]))

def betweenWeight (f : Finset V → ℝ) (a b : V) (l : List V) : ℝ :=
  SpinGlass.ColorPath.weight (fun x => f {a,x}) (fun x y => f {x,y}) l *
    l.head?.elim 0 (fun x => f {x,b})

theorem between_list_nodup {a b : V} {l : List V} (hab : a≠b)
    (hl : l.Nodup) (ha : a∉l) (hb : b∉l) : (b::(l++[a])).Nodup := by
  apply List.nodup_cons.mpr
  exact ⟨by simpa using And.intro hb hab.symm, nodup_append_root hl ha⟩

/-- Fixed distinct branch endpoints remove all orientation ambiguity. -/
theorem betweenEdges_injective {a b : V} {l q : List V} (hab : a≠b)
    (hl : l.Nodup) (hq : q.Nodup) (hal : a∉l) (hbl : b∉l) (haq : a∉q) (hbq : b∉q)
    (he : betweenEdges a b l=betweenEdges a b q) : l=q := by
  have h := pathEdges_head_injective (between_list_nodup hab hl hal hbl)
    (between_list_nodup hab hq haq hbq) rfl he
  exact List.append_cancel_right (List.cons.inj h).2

/-- Every branch-to-branch chain has exactly its signed graph weight. -/
theorem betweenWeight_eq_product (f : Finset V → ℝ) {a b : V} {l : List V}
    (hab : a≠b) (hl : l.Nodup) (ha : a∉l) (hb : b∉l) (hne : l≠[]) :
    betweenWeight f a b l=∏ e∈betweenEdges a b l, f e := by
  obtain ⟨x,xs,rfl⟩ := List.exists_cons_of_ne_nil hne
  have hbl : b∉(x::xs)++[a] := by
    simpa only [List.mem_append, List.mem_singleton, not_or] using And.intro hb hab.symm
  rw [betweenWeight, SpinGlass.ColorCycleChain.weight_factor_start_last,
    chainWeight_eq_product f hl (by simp),
    List.getLast?_eq_some_getLast (l:=x::xs) (by simp)]
  simp only [Option.elim_some, List.head?_cons]
  change _ = ∏ e∈insert {b,x} (pathEdges ((x::xs)++[a])), f e
  rw [Finset.prod_insert (not_mem_pathEdges hbl (by simp)), pathEdges_concat,
    Finset.prod_insert (not_mem_pathEdges ha (by simp))]
  rw [Finset.pair_comm ((x::xs).getLast (by simp)) a, Finset.pair_comm x b]
  ring

/-- No normalization factor is needed for a path between distinct branch vertices. -/
theorem between_sum (f : Finset V → ℝ) (F : Finset (List V)) {a b : V} (hab : a≠b)
    (hn : ∀ l∈F, l.Nodup) (ha : ∀ l∈F, a∉l) (hb : ∀ l∈F, b∉l)
    (hne : ∀ l∈F, l≠[]) :
    (∑ l∈F, betweenWeight f a b l)=∑ Γ∈F.image (betweenEdges a b), ∏ e∈Γ, f e := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro l hl
    exact betweenWeight_eq_product f hab (hn l hl) (ha l hl) (hb l hl) (hne l hl)
  · intro l hl q hq he
    exact betweenEdges_injective hab (hn l hl) (hn q hq) (ha l hl) (hb l hl)
      (ha q hq) (hb q hq) he

end SpinGlass.SKTraversal
