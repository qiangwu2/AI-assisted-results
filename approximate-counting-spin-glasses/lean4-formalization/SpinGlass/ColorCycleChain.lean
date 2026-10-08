import SpinGlass.ColorPath

/-!
# The rooted-chain recurrence used for outside cycles

This file derives recurrence (68) from the verified generic color-subset table,
including all zero-state constraints. It does not assume cycle normalization or
identify chain orbits with graph components.
-/

noncomputable section

namespace SpinGlass.ColorCycleChain

open scoped BigOperators
open ColorPath

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- The one-hot initial register for a chain rooted at `r`. -/
def rootStart (r : V) (i : V) : ℝ := if i = r then 1 else 0

/-- The outside-root chain table `D_r(S,j)` in (68). -/
def rootTable (χ : V → C) (w : V → V → ℝ) (r : V) (S : Finset C) (j : V) : ℝ :=
  pathTable χ (rootStart r) w S j

/-- Zero start values on the allowed colors propagate through every update. -/
theorem table_eq_zero_of_start_zero (χ : V → C) (start : V → ℝ)
    (w : V → V → ℝ) (n : ℕ) (S : Finset C) (j : V)
    (hstart : ∀ i, χ i ∈ S → start i = 0) : table χ start w n S j = 0 := by
  induction n generalizing S j with
  | zero => rfl
  | succ n ih =>
    simp only [table]
    split
    next hS => exact hstart j (by simp [hS])
    next hS =>
      split
      next hj =>
        apply Finset.sum_eq_zero
        intro i hi
        rw [ih (S.erase (χ j)) i]
        · simp
        · intro k hk
          exact hstart k (Finset.mem_of_mem_erase hk)
      next hj => rfl

/-- The root color must occur in every nonzero state. -/
theorem rootTable_root_missing (χ : V → C) (w : V → V → ℝ)
    (r : V) (S : Finset C) (j : V) (hr : χ r ∉ S) : rootTable χ w r S j = 0 := by
  unfold rootTable pathTable
  apply table_eq_zero_of_start_zero
  intro i hi
  have hne : i ≠ r := by intro heq; subst i; contradiction
  simp [rootStart, hne]

/-- A nonzero endpoint must have a color in the subset. -/
theorem rootTable_endpoint_missing (χ : V → C) (w : V → V → ℝ)
    (r : V) (S : Finset C) (j : V) (hj : χ j ∉ S) : rootTable χ w r S j = 0 :=
  pathTable_invalid χ (rootStart r) w S j hj

/-- Larger states cannot return to the root color. -/
theorem rootTable_endpoint_root_color (χ : V → C) (w : V → V → ℝ)
    (r : V) (S : Finset C) (j : V) (hc : χ j = χ r) (hsize : 2 ≤ S.card) :
    rootTable χ w r S j = 0 := by
  by_cases hj : χ j ∈ S
  · unfold rootTable
    rw [pathTable_recurrence χ (rootStart r) w S j hj hsize]
    apply Finset.sum_eq_zero
    intro i hi
    change rootTable χ w r (S.erase (χ j)) i * w i j = 0
    rw [rootTable_root_missing χ w r (S.erase (χ j)) i]
    · simp
    · simpa [hc] using Finset.notMem_erase (χ r) S
  · exact rootTable_endpoint_missing χ w r S j hj

/-- All singleton states are exactly the one-hot initialization in the paper. -/
theorem rootTable_singleton (χ : V → C) (w : V → V → ℝ) (r j : V) (c : C) :
    rootTable χ w r {c} j = if j = r ∧ χ r = c then 1 else 0 := by
  by_cases hc : χ j = c
  · have heq : ({c} : Finset C) = {χ j} := by rw [hc]
    rw [rootTable, heq, pathTable_singleton]
    by_cases hj : j = r <;> simp_all [rootStart]
  · rw [rootTable_endpoint_missing χ w r {c} j (by simpa using hc)]
    have hnot : ¬ (j = r ∧ χ r = c) := by rintro ⟨rfl, h⟩; contradiction
    simp [hnot]

/-- The nonzero update states satisfy exactly recurrence (68). -/
theorem rootTable_recurrence (χ : V → C) (w : V → V → ℝ)
    (r : V) (S : Finset C) (j : V) (hj : χ j ∈ S) (hsize : 2 ≤ S.card) :
    rootTable χ w r S j = ∑ i, rootTable χ w r (S.erase (χ j)) i * w i j :=
  pathTable_recurrence χ (rootStart r) w S j hj hsize

/-- A chain's initial weight appears only at its final list element. -/
theorem weight_factor_start_last (start : V → ℝ) (w : V → V → ℝ) (l : List V) :
    weight start w l = (l.getLast?.elim 0 start) * weight (fun _ => 1) w l := by
  induction l with
  | nil => simp [weight]
  | cons j rest ih =>
    cases rest with
    | nil => simp [weight]
    | cons i rest =>
      simp only [weight]
      rw [ih]
      simp only [List.getLast?_cons_cons]
      ring

/-- Only chains whose starting vertex is the specified root can contribute. -/
theorem root_weight (r : V) (w : V → V → ℝ) (l : List V) :
    weight (rootStart r) w l =
      if l.getLast? = some r then weight (fun _ => 1) w l else 0 := by
  rw [weight_factor_start_last]
  cases hlast : l.getLast? with
  | none => simp
  | some i =>
    by_cases hi : i = r <;> simp [rootStart, hi]

/-- The `D` recurrence is an exact sum over all rooted colorful simple chains. -/
theorem rootTable_eq_rooted_chain_sum (χ : V → C) (w : V → V → ℝ)
    (r : V) (S : Finset C) (j : V) :
    rootTable χ w r S j =
      ∑ l ∈ ((chains χ S.card S j).toFinset.filter (fun l => l.getLast? = some r)),
        weight (fun _ => 1) w l := by
  rw [rootTable, pathTable_eq_finset_chain_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  exact root_weight r w l

end SpinGlass.ColorCycleChain
