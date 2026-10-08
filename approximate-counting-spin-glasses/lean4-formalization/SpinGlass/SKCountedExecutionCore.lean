import SpinGlass.ArithmeticEvaluation
import SpinGlass.ColorMemoExecution

/-! A finite cache execution model: each scheduled computation is executed once,
stored by a point update, and subsequent table reads are literal accesses. -/
noncomputable section
namespace SpinGlass.SKCountedExecution
open scoped BigOperators
open SpinGlass.ArithmeticEvaluation

structure Counted (α : Type*) where
  value : α
  operations : ℕ

def ofComputation (x : Computation) : Counted ℝ := ⟨x.value, x.operations⟩

def cacheStep {I α : Type*} [DecidableEq I] (program : I → Counted α)
    (i : I) (state : Counted (I → α)) : Counted (I → α) :=
  let result := program i
  ⟨Function.update state.value i result.value, state.operations + result.operations⟩

def cacheLoop {I α : Type*} [DecidableEq I] (program : I → Counted α) :
    List I → Counted (I → α) → Counted (I → α)
  | [], state => state
  | i :: is, state => cacheLoop program is (cacheStep program i state)

theorem cacheLoop_lookup {I α : Type*} [DecidableEq I] (program : I → Counted α)
    (is : List I) (state : Counted (I → α)) (i : I) :
    (cacheLoop program is state).value i = if i ∈ is then (program i).value else state.value i := by
  induction is generalizing state with
  | nil => simp [cacheLoop]
  | cons j js ih =>
    rw [cacheLoop, ih]
    by_cases hi : i ∈ js
    · simp [hi]
    · by_cases hij : i = j
      · subst j
        simp [hi, cacheStep]
      · simp [hi, hij, cacheStep, Function.update_of_ne hij]

theorem cacheLoop_operations {I α : Type*} [DecidableEq I] (program : I → Counted α)
    (is : List I) (state : Counted (I → α)) :
    (cacheLoop program is state).operations = state.operations + (is.map (fun i => (program i).operations)).sum := by
  induction is generalizing state with
  | nil => simp [cacheLoop]
  | cons i is ih => simp [cacheLoop, ih, cacheStep, Nat.add_assoc]

/-- Explicit once-per-index point-update tabulation. -/
def tabulate {I α : Type*} [Fintype I] [DecidableEq I] [Inhabited α]
    (program : I → Counted α) : Counted (I → α) :=
  cacheLoop program Finset.univ.toList ⟨fun _ => default, 0⟩

@[simp] theorem tabulate_value {I α : Type*} [Fintype I] [DecidableEq I] [Inhabited α]
    (program : I → Counted α) (i : I) : (tabulate program).value i = (program i).value := by
  simp [tabulate, cacheLoop_lookup]

@[simp] theorem tabulate_operations {I α : Type*} [Fintype I] [DecidableEq I] [Inhabited α]
    (program : I → Counted α) : (tabulate program).operations = ∑ i, (program i).operations := by
  simp [tabulate, cacheLoop_operations]

variable {W : Type*} [Fintype W] [DecidableEq W]

abbrev Table (W : Type*) (L : ℕ) := Finset (Fin L) → W → ℝ

/-- A single recurrence computation reads every predecessor from a saved table. -/
def memoCell {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (old : Table W L) (S : Finset (Fin L)) (j : W) : Computation :=
  if S = {χ j} then literal (start j)
  else if χ j ∈ S then
    sumFinset Finset.univ (fun i => mul (literal (old (S.erase (χ j)) i)) (literal (w i j)))
  else literal 0

@[simp] theorem memoCell_value {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (old : Table W L) (S : Finset (Fin L)) (j : W) :
    (memoCell χ start w old S j).value = SpinGlass.ColorMemoExecution.update χ start w old S j := by
  unfold memoCell SpinGlass.ColorMemoExecution.update
  split_ifs <;> simp [literal, mul]

theorem memoCell_operations_le {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (old : Table W L) (S : Finset (Fin L)) (j : W) :
    (memoCell χ start w old S j).operations ≤ 2 * Fintype.card W := by
  unfold memoCell
  split_ifs <;> simp [literal, mul, sumFinset_operations] <;> omega

/-- A complete saved layer is materialized by a finite cache traversal. -/
def memoPass {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (n : ℕ) (old : Table W L) : Counted (Table W L) :=
  let cells := tabulate (fun p : Finset (Fin L) × W =>
    ofComputation (if p.1.card = n then memoCell χ start w old p.1 p.2 else literal (old p.1 p.2)))
  ⟨fun S j => cells.value (S, j), cells.operations⟩

theorem memoPass_value {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (n : ℕ) (old : Table W L) (S : Finset (Fin L)) (j : W) :
    (memoPass χ start w n old).value S j =
      if S.card = n then SpinGlass.ColorMemoExecution.update χ start w old S j else old S j := by
  simp only [memoPass, tabulate_value, ofComputation]
  split_ifs <;> simp [literal]

theorem memoPass_operations_le {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (n : ℕ) (old : Table W L) :
    (memoPass χ start w n old).operations ≤ 2 * 2 ^ L * (Fintype.card W) ^ 2 := by
  unfold memoPass
  rw [tabulate_operations]
  calc
    _ ≤ ∑ _p : Finset (Fin L) × W, 2 * Fintype.card W := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp [ofComputation]
      split_ifs
      · exact memoCell_operations_le _ _ _ _ _ _
      · simp [literal]
    _ = _ := by simp [Fintype.card_prod]; ring

/-- The recursion stores each completed layer before the next layer begins. -/
def memo {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ) :
    ℕ → Counted (Table W L)
  | 0 => ⟨fun _ _ => 0, 0⟩
  | n + 1 =>
    let old := memo χ start w n
    let layer := memoPass χ start w (n + 1) old.value
    ⟨layer.value, old.operations + layer.operations⟩

theorem memo_value {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (n : ℕ) : (memo χ start w n).value = SpinGlass.ColorMemoExecution.memo χ start w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext S j
    simp only [memo, memoPass_value, ih, SpinGlass.ColorMemoExecution.memo]

theorem memo_operations_le {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (n : ℕ) : (memo χ start w n).operations ≤ n * (2 * 2 ^ L * (Fintype.card W) ^ 2) := by
  induction n with
  | zero => simp [memo]
  | succ n ih =>
    change (memo χ start w n).operations + (memoPass χ start w (n + 1) (memo χ start w n).value).operations ≤ _
    have h := memoPass_operations_le χ start w (n + 1) (memo χ start w n).value
    nlinarith

end SpinGlass.SKCountedExecution
