import SpinGlass.SKPrimitiveMonomials
import SpinGlass.SKColorfulCatalog

/-! # Exact coordinate identities for every member of the actual finite catalogs -/
noncomputable section
namespace SpinGlass.SKPrimitiveMonomials
open scoped BigOperators
open SKGraphMonomial SKRing SKFastEvaluator SKActualEvaluator SKTraversal SKColorfulCatalog
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem path_value {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (a c : Fin A.card) (hac : a ≠ c) (S : Finset (Fin L))
    {Γ : Finset (Finset V)} (hΓ : Γ ∈ pathCatalog A χ a c S) :
    value id A (branch A) (totalColor A χ hL) f Γ =
      insertMonomial (S.card + 1) S (pathDegrees a c) (∏ e ∈ Γ, f e) := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
  have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
  have ho := lifted_list_outside A χ S hl
  have hroot : ∀ d, branch A d ∉ l := fun d hm => ho _ hm (branch_mem A d)
  apply value_of_coordinates
  · rw [betweenEdges_card (fun h => hac (branch_injective A h)) hn (hroot a) (hroot c),
      liftedChains_length Subtype.val χ S hl]
  · rw [colors, path_outside A χ a c S hl]
    exact lifted_list_colors A χ hL S hl
  · rw [Colorful, path_outside A χ a c S hl]
    exact lifted_list_colorful A χ hL S hl
  · exact between_degrees A a c hac l hn ho

theorem return_value {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (a : Fin A.card) (S : Finset (Fin L)) (hS : 2 ≤ S.card)
    {Γ : Finset (Finset V)} (hΓ : Γ ∈ returnCatalog A χ a S) :
    value id A (branch A) (totalColor A χ hL) f Γ =
      insertMonomial (S.card + 1) S (pathDegrees a a) (∏ e ∈ Γ, f e) := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
  have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
  have ho := lifted_list_outside A χ S hl
  have hlen : 2 ≤ l.length := by simpa [liftedChains_length Subtype.val χ S hl] using hS
  have hroot : branch A a ∉ l := fun hm => ho _ hm (branch_mem A a)
  apply value_of_coordinates
  · rw [rootedEdges_card hn hroot hlen, liftedChains_length Subtype.val χ S hl]
  · rw [colors, return_outside A χ a S hl]
    exact lifted_list_colors A χ hL S hl
  · rw [Colorful, return_outside A χ a S hl]
    exact lifted_list_colorful A χ hL S hl
  · exact return_degrees A a l hn ho hlen

theorem cycle_value {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (S : Finset (Fin L)) (hS : 3 ≤ S.card)
    {Γ : Finset (Finset V)} (hΓ : Γ ∈ cycleCatalog A χ S) :
    value id A (branch A) (totalColor A χ hL) f Γ =
      insertMonomial S.card S (fun _ => 0) (∏ e ∈ Γ, f e) := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
  have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
  have ho := lifted_list_outside A χ S hl
  have hlen : 3 ≤ l.length := by simpa [liftedChains_length Subtype.val χ S hl] using hS
  apply value_of_coordinates
  · rw [cycleEdges_card hn hlen, liftedChains_length Subtype.val χ S hl]
  · rw [colors, cycle_outside A χ S hl]
    exact lifted_list_colors A χ hL S hl
  · rw [Colorful, cycle_outside A χ S hl]
    exact lifted_list_colorful A χ hL S hl
  · exact cycle_degrees A l hn ho hlen

theorem branch_not_range (A : Finset V) (a : Fin A.card) :
    branch A a ∉ Set.range (Subtype.val : Outside A → V) := by
  rintro ⟨v,hv⟩
  exact v.property (hv.symm ▸ branch_mem A a)

/-- Actual path DP output inserts exactly one copy of every signed path graph. -/
theorem path_sum {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (a c : Fin A.card) (hac : a ≠ c) (S : Finset (Fin L)) :
    insertMonomial (S.card + 1) S (pathDegrees a c)
      (pathCoefficient (branch A) Subtype.val χ f a c S) =
      ∑ Γ ∈ pathCatalog A χ a c S, value id A (branch A) (totalColor A χ hL) f Γ := by
  rw [pathCoefficient_eq]
  change insertMonomial _ _ _ (SKPrimitiveTables.pathClosure χ
    (fun i => f {branch A a,i.val}) (fun i j => f {i.val,j.val})
    (fun j => f {j.val,branch A c}) S) = _
  rw [pathClosure_eq_graph_sum Subtype.val (outside_injective A) χ S f
    (fun h => hac (branch_injective A h)) (branch_not_range A a) (branch_not_range A c)]
  rw [insertMonomial_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  exact (path_value A χ hL f a c hac S hΓ).symm

/-- The two-orientation-normalized return table inserts its precise graph sum. -/
theorem return_sum {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (a : Fin A.card) (S : Finset (Fin L)) (hS : 2 ≤ S.card) :
    insertMonomial (S.card + 1) S (pathDegrees a a)
      (returnCoefficient (branch A) Subtype.val χ f a S) =
      ∑ Γ ∈ returnCatalog A χ a S, value id A (branch A) (totalColor A χ hL) f Γ := by
  rw [returnCoefficient_eq]
  change insertMonomial _ _ _ (SKPrimitiveTables.rootedClosure χ
    (fun i => f {branch A a,i.val}) (fun i j => f {i.val,j.val})
    (fun j => f {j.val,branch A a}) S) = _
  rw [rootedClosure_eq_graph_sum Subtype.val (outside_injective A) χ S f
    (branch_not_range A a) hS, insertMonomial_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  exact (return_value A χ hL f a S hS hΓ).symm

/-- The full root-and-orientation-normalized cycle table inserts its precise graph sum. -/
theorem cycle_sum {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (S : Finset (Fin L)) (hS : 3 ≤ S.card) :
    insertMonomial S.card S (fun _ => 0) (cycleCoefficient Subtype.val χ f S) =
      ∑ Γ ∈ cycleCatalog A χ S, value id A (branch A) (totalColor A χ hL) f Γ := by
  rw [cycleCoefficient_eq]
  change insertMonomial _ _ _ (SKPrimitiveTables.outsideClosure χ
    (fun i j => f {i.val,j.val}) S) = _
  rw [outsideClosure_eq_graph_sum Subtype.val (outside_injective A) χ S f hS,
    insertMonomial_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  exact (cycle_value A χ hL f S hS hΓ).symm

end SpinGlass.SKPrimitiveMonomials
