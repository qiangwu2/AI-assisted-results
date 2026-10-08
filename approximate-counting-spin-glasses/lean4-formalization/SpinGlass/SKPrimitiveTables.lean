import SpinGlass.ColorCycleChain
import SpinGlass.SKGraphMonomial

/-!
# Actual primitive closure tables

Equations (66)--(69) are assembled from the proved path recurrences. These
identities identify their literal finite traversal sums; orientation-to-graph
normalization is established separately in the traversal modules.
-/

noncomputable section
namespace SpinGlass.SKPrimitiveTables

open scoped BigOperators
open ColorPath
variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- All colorful nonempty ordered chains, partitioned by their final endpoint. -/
def allChains (χ : V → C) (S : Finset C) : Finset (List V) :=
  Finset.univ.biUnion (fun j => (chains χ S.card S j).toFinset)

/-- There is no hidden traversal restriction beyond distinct colors and exact support. -/
theorem mem_allChains (χ : V → C) (S : Finset C) (l : List V) :
    l ∈ allChains χ S ↔ l ≠ [] ∧ (l.map χ).Nodup ∧ (l.map χ).toFinset = S := by
  simp only [allChains, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_canonical_chains_iff]
  constructor
  · rintro ⟨j, hh, hn, hS⟩
    exact ⟨by intro h; simp [h] at hh, hn, hS⟩
  · rintro ⟨hne, hn, hS⟩
    cases l with
    | nil => contradiction
    | cons j l => exact ⟨j, rfl, hn, hS⟩

/-- A chain belongs to one endpoint's table only. -/
theorem chains_disjoint (χ : V → C) (S : Finset C) {i j : V} (hij : i ≠ j) :
    Disjoint (chains χ S.card S i).toFinset (chains χ S.card S j).toFinset := by
  apply Finset.disjoint_left.mpr
  intro l hi hj
  have hhi := (mem_canonical_chains_iff χ S i l).mp hi
  have hhj := (mem_canonical_chains_iff χ S j l).mp hj
  exact hij (Option.some.inj (hhi.1.symm.trans hhj.1))

/-- Literal endpoint closure used for both branch-to-branch paths and return cycles. -/
def pathClosure (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (finish : V → ℝ) (S : Finset C) : ℝ :=
  ∑ j, pathTable χ start w S j * finish j

/-- The closure sums every ordered colorful chain exactly once. -/
theorem pathClosure_eq_chain_sum (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (finish : V → ℝ) (S : Finset C) :
    pathClosure χ start w finish S = ∑ l ∈ allChains χ S,
      weight start w l * l.head?.elim 0 finish := by
  rw [allChains, Finset.sum_biUnion]
  · unfold pathClosure
    apply Finset.sum_congr rfl
    intro j hj
    rw [pathTable_eq_finset_chain_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    rw [((mem_canonical_chains_iff χ S j l).mp hl).1]
    rfl
  · intro i hi j hj hij
    exact chains_disjoint χ S hij

/-- Equation (67), with its simple-cycle minimum length. -/
def rootedClosure (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (finish : V → ℝ) (S : Finset C) : ℝ :=
  if 2 ≤ S.card then (2 : ℝ)⁻¹ * pathClosure χ start w finish S else 0

/-- Equation (69), including both root and endpoint sums. -/
def outsideClosure (χ : V → C) (w : V → V → ℝ) (S : Finset C) : ℝ :=
  if 3 ≤ S.card then (2 * S.card : ℝ)⁻¹ *
    ∑ r, ∑ j, ColorCycleChain.rootTable χ w r S j * w j r else 0

/-- Root summation restores the chain's actual starting endpoint once. -/
theorem sum_root_closures (χ : V → C) (w : V → V → ℝ) (S : Finset C) :
    (∑ r, ∑ j, ColorCycleChain.rootTable χ w r S j * w j r) =
      ∑ l ∈ allChains χ S, weight (fun _ => 1) w l *
        (l.head?.bind (fun j => l.getLast?.map (fun r => w j r))).getD 0 := by
  have hp : ∀ r, (∑ j, ColorCycleChain.rootTable χ w r S j * w j r) =
      ∑ l ∈ allChains χ S, weight (ColorCycleChain.rootStart r) w l *
        l.head?.elim 0 (fun j => w j r) := fun r =>
    pathClosure_eq_chain_sum χ (ColorCycleChain.rootStart r) w (fun j => w j r) S
  simp_rw [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  have hne := (mem_allChains χ S l).mp hl |>.1
  obtain ⟨j, js, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hlast : ∃ r, (j :: js).getLast? = some r :=
    ⟨(j :: js).getLast (by simp), List.getLast?_eq_some_getLast (by simp)⟩
  obtain ⟨r, hr⟩ := hlast
  simp [ColorCycleChain.root_weight, hr]

/-- Actual root-normalized outside closure as a finite signed traversal sum. -/
theorem outsideClosure_eq_chain_sum (χ : V → C) (w : V → V → ℝ) (S : Finset C)
    (hS : 3 ≤ S.card) :
    outsideClosure χ w S = (2 * S.card : ℝ)⁻¹ *
      ∑ l ∈ allChains χ S, weight (fun _ => 1) w l *
        (l.head?.bind (fun j => l.getLast?.map (fun r => w j r))).getD 0 := by
  rw [outsideClosure, if_pos hS, sum_root_closures]

end SpinGlass.SKPrimitiveTables
