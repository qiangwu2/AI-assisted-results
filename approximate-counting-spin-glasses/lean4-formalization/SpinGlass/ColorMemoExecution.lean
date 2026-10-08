import SpinGlass.ColorPath

/-!
# Increasing-cardinality execution of the path table

Each pass fills one subset-cardinality layer from the saved preceding table.
Every predecessor access is to that preceding table, so no predecessor subtree
is recursively recomputed during a state update.
-/

noncomputable section
namespace SpinGlass.ColorMemoExecution

open scoped BigOperators
open ColorPath
variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- One recurrence update, reading exclusively from the previous saved table. -/
def update (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (old : Finset C → V → ℝ) (S : Finset C) (j : V) : ℝ :=
  if S = {χ j} then start j
  else if χ j ∈ S then ∑ i, old (S.erase (χ j)) i * w i j else 0

/-- Saved tables after successively filling cardinality layers. -/
def memo (χ : V → C) (start : V → ℝ) (w : V → V → ℝ) :
    ℕ → Finset C → V → ℝ
  | 0, _, _ => 0
  | n + 1, S, j =>
      let old := memo χ start w n
      if S.card = n + 1 then update χ start w old S j else old S j

@[simp] theorem pathTable_empty (χ : V → C) (start : V → ℝ)
    (w : V → V → ℝ) (j : V) : pathTable χ start w ∅ j = 0 := by
  simp [pathTable, table]

/-- Every finished layer equals the exact colorful-chain sum. -/
theorem memo_invariant (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (n : ℕ) (S : Finset C) (j : V) :
    memo χ start w n S j = if S.card ≤ n then pathTable χ start w S j else 0 := by
  induction n generalizing S j with
  | zero =>
    by_cases h : S = ∅
    · simp [memo, h]
    · have hc : ¬ S.card ≤ 0 := by simpa using h
      simp [memo, hc]
  | succ n ih =>
    by_cases hc : S.card = n + 1
    · rw [memo, if_pos hc, if_pos (by omega)]
      unfold update
      by_cases hs : S = {χ j}
      · simp [hs]
      · by_cases hj : χ j ∈ S
        · have he : (S.erase (χ j)).card = n := by
            rw [Finset.card_erase_of_mem hj, hc]
            omega
          simp only [if_neg hs, if_pos hj]
          simp_rw [ih, if_pos (Nat.le_of_eq he)]
          change (∑ i, pathTable χ start w (S.erase (χ j)) i * w i j) = _
          have hn : 2 ≤ S.card := by
            have hpos : 0 < S.card := Finset.card_pos.mpr ⟨χ j, hj⟩
            by_contra h
            have hcard1 : S.card = 1 := by omega
            obtain ⟨c, hSc⟩ := Finset.card_eq_one.mp hcard1
            have hχ : χ j = c := by simpa [hSc] using hj
            exact hs (by simpa [hχ] using hSc)
          exact (pathTable_recurrence χ start w S j hj hn).symm
        · simp only [if_neg hs, if_neg hj]
          exact (pathTable_invalid χ start w S j hj).symm
    · rw [memo, if_neg hc, ih]
      have hle : S.card ≤ n + 1 ↔ S.card ≤ n := by omega
      simp only [hle]

/-- All subsets are complete after as many passes as there are colors. -/
theorem memo_correct [Fintype C] (χ : V → C) (start : V → ℝ)
    (w : V → V → ℝ) (S : Finset C) (j : V) :
    memo χ start w (Fintype.card C) S j = pathTable χ start w S j := by
  rw [memo_invariant, if_pos (Finset.card_le_univ S)]

/-- Scheduled table cells, including copied and invalid states, per cardinality pass. -/
def stateVisits (N L : ℕ) : ℕ :=
  L * Fintype.card (Finset (Fin L) × Fin N)

/-- Each nontrivial state tries at most every predecessor vertex. -/
def predecessorVisits (N L : ℕ) : ℕ :=
  L * Fintype.card (Finset (Fin L) × Fin N × Fin N)

theorem stateVisits_exact (N L : ℕ) : stateVisits N L = L * 2 ^ L * N := by
  rw [stateVisits, table_state_count]
  exact (Nat.mul_assoc _ _ _).symm

theorem predecessorVisits_exact (N L : ℕ) :
    predecessorVisits N L = L * 2 ^ L * N ^ 2 := by
  rw [predecessorVisits, table_update_count]
  exact (Nat.mul_assoc _ _ _).symm

/-- A multiply and accumulation per predecessor suffice for all signed recurrence updates. -/
theorem arithmetic_bound (N L : ℕ) :
    2 * predecessorVisits N L = 2 * L * 2 ^ L * N ^ 2 := by
  rw [predecessorVisits_exact]
  ring

end SpinGlass.ColorMemoExecution
