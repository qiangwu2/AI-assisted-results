import SpinGlass.SKTraversalFiniteClosure
import SpinGlass.SKPrimitiveTables

/-!
# Exact primitive graph sums computed by the actual colorful closure tables

The outside vertex type may differ from the ambient vertex type. Its injective
inclusion is explicit, and branch roots are required to lie outside its range.
-/
noncomputable section
namespace SpinGlass.SKTraversal
open Finset SpinGlass.SKPrimitiveTables
variable {V W C : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [DecidableEq C]

/-- The exact ambient vertex lists represented by the outside dynamic program. -/
def liftedChains (ι : W → V) (χ : W → C) (S : Finset C) : Finset (List V) :=
  (allChains χ S).image (List.map ι)

theorem allChains_nodup (χ : W → C) (S : Finset C) {l : List W} (hl : l∈allChains χ S) :
    l.Nodup := List.Nodup.of_map χ ((mem_allChains χ S l).mp hl).2.1

theorem allChains_length (χ : W → C) (S : Finset C) {l : List W} (hl : l∈allChains χ S) :
    l.length=S.card := by
  have h := (mem_allChains χ S l).mp hl
  have he := List.toFinset_card_of_nodup h.2.1
  simpa only [h.2.2, List.length_map] using he.symm

theorem allChains_closed (χ : W → C) (S : Finset C) : PermutationClosed (allChains χ S) := by
  intro l hl q hp
  obtain ⟨hne,hn,hS⟩ := (mem_allChains χ S l).mp hl
  apply (mem_allChains χ S q).mpr
  refine ⟨?_,(hp.map χ).nodup_iff.mpr hn, ?_⟩
  · intro h; subst q; exact hne (List.length_eq_zero_iff.mp hp.length_eq.symm)
  · rw [← hS]
    ext c
    simpa only [List.mem_toFinset] using (hp.map χ).mem_iff

private theorem exists_preimage_list (ι : W → V) (q : List V)
    (hq : ∀ v∈q, ∃ w, ι w=v) : ∃ l : List W, l.map ι=q := by
  induction q with
  | nil => exact ⟨[],rfl⟩
  | cons v q ih =>
    obtain ⟨w,rfl⟩ := hq v (by simp)
    obtain ⟨l,hl⟩ := ih (fun v hv => hq v (List.mem_cons_of_mem _ hv))
    exact ⟨w::l,by simp [hl]⟩

theorem liftedChains_nodup (ι : W → V) (hι : Function.Injective ι) (χ : W → C) (S : Finset C)
    {l : List V} (hl : l∈liftedChains ι χ S) : l.Nodup := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hl
  exact (allChains_nodup χ S hq).map hι

theorem liftedChains_length (ι : W → V) (χ : W → C) (S : Finset C)
    {l : List V} (hl : l∈liftedChains ι χ S) : l.length=S.card := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hl
  simpa only [List.length_map] using allChains_length χ S hq

theorem liftedChains_nonempty (ι : W → V) (χ : W → C) (S : Finset C)
    {l : List V} (hl : l∈liftedChains ι χ S) : l≠[] := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hl
  simpa using ((mem_allChains χ S q).mp hq).1

theorem liftedChains_avoid (ι : W → V) (χ : W → C) (S : Finset C)
    {root : V} (hr : root∉Set.range ι) {l : List V} (hl : l∈liftedChains ι χ S) : root∉l := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hl
  intro h
  obtain ⟨v,hv,he⟩ := List.mem_map.mp h
  exact hr ⟨v,he⟩

/-- Lifting along an injection preserves completeness under every vertex permutation. -/
theorem liftedChains_closed (ι : W → V) (hι : Function.Injective ι) (χ : W → C) (S : Finset C) :
    PermutationClosed (liftedChains ι χ S) := by
  intro l hl q hp
  obtain ⟨l',hl',rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨q',he⟩ := exists_preimage_list ι q (fun v hv => by
    obtain ⟨w,hw,he⟩ := List.mem_map.mp (hp.mem_iff.mp hv)
    exact ⟨w,he⟩)
  have hqn : q'.Nodup := List.Nodup.of_map ι (by
    rw [he]
    exact hp.nodup_iff.mpr ((allChains_nodup χ S hl').map hι))
  have hperm : q'.Perm l' := by
    apply List.perm_of_nodup_nodup_toFinset_eq hqn (allChains_nodup χ S hl')
    ext w
    simp only [List.mem_toFinset]
    have hmem : w∈q' ↔ ι w∈q := by
      rw [← he, List.mem_map]
      constructor
      · intro h; exact ⟨w,h,rfl⟩
      · rintro ⟨z,hz,hz'⟩; exact hι hz' ▸ hz
    rw [hmem, hp.mem_iff, List.mem_map]
    constructor
    · rintro ⟨z,hz,hz'⟩; exact hι hz' ▸ hz
    · intro h; exact ⟨w,h,rfl⟩
  exact Finset.mem_image.mpr ⟨q',allChains_closed χ S l' hl' q' hperm,he⟩

/-- Relabeling a chain commutes with the literal path-weight recursion. -/
theorem chainWeight_map (ι : W → V) (start : V → ℝ) (w : V → V → ℝ) (l : List W) :
    SpinGlass.ColorPath.weight (fun x => start (ι x)) (fun x y => w (ι x) (ι y)) l =
      SpinGlass.ColorPath.weight start w (l.map ι) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons y l => simp only [SpinGlass.ColorPath.weight, List.map_cons, ih]

/-- The branch-to-branch table is exactly the ambient mapped chain sum. -/
theorem pathClosure_eq_lifted_sum (ι : W → V) (hι : Function.Injective ι)
    (χ : W → C) (S : Finset C) (f : Finset V → ℝ) (a b : V) :
    pathClosure χ (fun i => f {a,ι i}) (fun i j => f {ι i,ι j}) (fun j => f {ι j,b}) S =
      ∑ l∈liftedChains ι χ S, betweenWeight f a b l := by
  rw [pathClosure_eq_chain_sum, liftedChains, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [betweenWeight, ← chainWeight_map ι (fun x => f {a,x}) (fun x y => f {x,y})]
    cases l <;> simp
  · intro l hl q hq h
    exact hι.list_map h

/-- Equation (66), with each genuine branch-to-branch graph counted once. -/
theorem pathClosure_eq_graph_sum (ι : W → V) (hι : Function.Injective ι)
    (χ : W → C) (S : Finset C) (f : Finset V → ℝ) {a b : V}
    (hab : a≠b) (ha : a∉Set.range ι) (hb : b∉Set.range ι) :
    pathClosure χ (fun i => f {a,ι i}) (fun i j => f {ι i,ι j}) (fun j => f {ι j,b}) S =
      ∑ Γ∈(liftedChains ι χ S).image (betweenEdges a b), ∏ e∈Γ, f e := by
  rw [pathClosure_eq_lifted_sum ι hι χ S f a b]
  exact between_sum f _ hab (fun l hl => liftedChains_nodup ι hι χ S hl)
    (fun l hl => liftedChains_avoid ι χ S ha hl)
    (fun l hl => liftedChains_avoid ι χ S hb hl)
    (fun l hl => liftedChains_nonempty ι χ S hl)

/-- Equation (67), with the orientation factor derived from actual graph fibers. -/
theorem rootedClosure_eq_graph_sum (ι : W → V) (hι : Function.Injective ι)
    (χ : W → C) (S : Finset C) (f : Finset V → ℝ) {a : V}
    (ha : a∉Set.range ι) (hS : 2≤S.card) :
    rootedClosure χ (fun i => f {a,ι i}) (fun i j => f {ι i,ι j}) (fun j => f {ι j,a}) S =
      ∑ Γ∈(liftedChains ι χ S).image (rootedEdges a), ∏ e∈Γ, f e := by
  rw [rootedClosure, if_pos hS, pathClosure_eq_lifted_sum ι hι χ S f a a]
  change (2:ℝ)⁻¹*(∑ l∈liftedChains ι χ S, returnWeight f a l)=_
  exact return_sum_normalized f _ (liftedChains_closed ι hι χ S)
    (fun l hl => liftedChains_nodup ι hι χ S hl)
    (fun l hl => liftedChains_avoid ι χ S ha hl)
    (fun l hl => by simpa [liftedChains_length ι χ S hl] using hS)

/-- Relabeling commutes with the head-to-tail closure of an outside cycle. -/
theorem cycleWeight_map (ι : W → V) (f : Finset V → ℝ) (l : List W) :
    SpinGlass.ColorPath.weight (fun _ => 1) (fun x y => f {ι x,ι y}) l *
      (l.head?.bind (fun x => l.getLast?.map (fun y => f {ι x,ι y}))).getD 0 =
      cycleWeight f (l.map ι) := by
  rw [cycleWeight, ← chainWeight_map ι (fun _ => 1) (fun x y => f {x,y})]
  rw [List.head?_map, List.getLast?_map]
  cases l.head? <;> cases l.getLast? <;> rfl

/-- Equation (69), with each outside cycle counted once across all roots and directions. -/
theorem outsideClosure_eq_graph_sum (ι : W → V) (hι : Function.Injective ι)
    (χ : W → C) (S : Finset C) (f : Finset V → ℝ) (hS : 3≤S.card) :
    outsideClosure χ (fun i j => f {ι i,ι j}) S =
      ∑ Γ∈(liftedChains ι χ S).image cycleEdges, ∏ e∈Γ, f e := by
  rw [outsideClosure_eq_chain_sum χ _ S hS]
  have he : (∑ l∈allChains χ S, SpinGlass.ColorPath.weight (fun _ => 1)
      (fun i j => f {ι i,ι j}) l *
      (l.head?.bind (fun j => l.getLast?.map (fun r => f {ι j,ι r}))).getD 0) =
      ∑ l∈liftedChains ι χ S, cycleWeight f l := by
    rw [liftedChains, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro l hl
      exact cycleWeight_map ι f l
    · intro l hl q hq h
      exact hι.list_map h
  rw [he]
  exact cycle_sum_normalized f _ (liftedChains_closed ι hι χ S)
    (fun l hl => liftedChains_nodup ι hι χ S hl) hS
    (fun l hl => liftedChains_length ι χ S hl)

end SpinGlass.SKTraversal
