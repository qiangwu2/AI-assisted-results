import SpinGlass.AlgorithmBudgets

/-! # Integer cutoffs computed using comparisons and increments

The floor/ceiling functions occur only in the well-founded termination proofs,
not in the executed branches or as an uncharged search bound. Each iteration
performs one comparison and, when continuing, one integer increment. -/
noncomputable section
namespace SpinGlass.RoundingExecution

structure Result where
  value : ℕ
  operations : ℕ

/-- Linear ceiling search in the exact-real unit-operation model. -/
def ceilFrom (x : ℝ) (n : ℕ) : Result :=
  if x ≤ (n : ℝ) then ⟨n, 1⟩ else
    let next := ceilFrom x (n+1)
    ⟨next.value, next.operations+2⟩
termination_by Nat.ceil x - n
decreasing_by
  have hn : n < Nat.ceil x := Nat.lt_ceil.mpr (lt_of_not_ge ‹¬x ≤ (n : ℝ)›)
  omega

/-- Linear floor search; the next integer is tested before incrementing. -/
def floorFrom (x : ℝ) (n : ℕ) : Result :=
  if (n+1 : ℕ) ≤ x then
    let next := floorFrom x (n+1)
    ⟨next.value, next.operations+2⟩
  else ⟨n, 1⟩
termination_by Nat.floor x - n
decreasing_by
  have hn : n+1 ≤ Nat.floor x := Nat.le_floor ‹((n+1 : ℕ) : ℝ) ≤ x›
  omega

/-- Exact value and exact number of comparisons/increments. -/
theorem ceilFrom_spec (x : ℝ) (n : ℕ) (hn : n ≤ Nat.ceil x) :
    (ceilFrom x n).value = Nat.ceil x ∧
      (ceilFrom x n).operations = 2*(Nat.ceil x-n)+1 := by
  have main : ∀ k n : ℕ, Nat.ceil x-n = k → n ≤ Nat.ceil x →
      (ceilFrom x n).value = Nat.ceil x ∧
      (ceilFrom x n).operations = 2*(Nat.ceil x-n)+1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hk hn
      rw [ceilFrom]
      split_ifs with hx
      · have hce : Nat.ceil x ≤ n := Nat.ceil_le.mpr hx
        have he : n = Nat.ceil x := by omega
        simp [he]
      · have hn' : n < Nat.ceil x := Nat.lt_ceil.mpr (lt_of_not_ge hx)
        have ht : Nat.ceil x-(n+1) < k := by omega
        have hs := ih _ ht (n+1) rfl (by omega)
        dsimp
        constructor
        · exact hs.1
        · rw [hs.2]
          omega
  exact main _ n rfl hn

theorem floorFrom_spec (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : n ≤ Nat.floor x) :
    (floorFrom x n).value = Nat.floor x ∧
      (floorFrom x n).operations = 2*(Nat.floor x-n)+1 := by
  have main : ∀ k n : ℕ, Nat.floor x-n = k → n ≤ Nat.floor x →
      (floorFrom x n).value = Nat.floor x ∧
      (floorFrom x n).operations = 2*(Nat.floor x-n)+1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hk hn
      rw [floorFrom]
      split_ifs with hnext
      · have hn' : n+1 ≤ Nat.floor x := Nat.le_floor hnext
        have ht : Nat.floor x-(n+1) < k := by omega
        have hs := ih _ ht (n+1) rfl hn'
        dsimp
        constructor
        · exact hs.1
        · rw [hs.2]
          omega
      · have hf : Nat.floor x < n+1 := (Nat.floor_lt hx).mpr (lt_of_not_ge hnext)
        have he : n = Nat.floor x := by omega
        simp [he]
  exact main _ n rfl hn

def ceiling (x : ℝ) : Result := ceilFrom x 0
def floor (x : ℝ) : Result := floorFrom x 0

@[simp] theorem ceiling_value (x : ℝ) : (ceiling x).value = Nat.ceil x :=
  (ceilFrom_spec x 0 (Nat.zero_le _)).1

@[simp] theorem ceiling_operations (x : ℝ) :
    (ceiling x).operations = 2*Nat.ceil x+1 := by
  simpa [ceiling] using (ceilFrom_spec x 0 (Nat.zero_le _)).2

@[simp] theorem floor_value (x : ℝ) (hx : 0 ≤ x) : (floor x).value = Nat.floor x :=
  (floorFrom_spec x hx 0 (Nat.zero_le _)).1

@[simp] theorem floor_operations (x : ℝ) (hx : 0 ≤ x) :
    (floor x).operations = 2*Nat.floor x+1 := by
  simpa [floor] using (floorFrom_spec x hx 0 (Nat.zero_le _)).2

/-- The branch scan's initialization takes linear time in the ambient size. -/
theorem floor_alpha_operations (N : ℕ) {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    (floor (alpha*N)).operations ≤ 2*N+1 := by
  rw [floor_operations _ (by positivity)]
  have hf : Nat.floor (alpha*N) ≤ N := Nat.floor_le_of_le (by
    have h := mul_le_mul_of_nonneg_right ha1 (Nat.cast_nonneg N : (0:ℝ)≤N)
    simpa using h)
  omega

/-- The scan initializer includes the multiplication forming its argument. -/
def floorSearch (N : ℕ) (alpha : ℝ) : Result :=
  let r := floor (alpha*N)
  ⟨r.value,r.operations+1⟩

@[simp] theorem floorSearch_value (N : ℕ) {alpha : ℝ} (ha : 0 ≤ alpha) :
    (floorSearch N alpha).value = Nat.floor (alpha*N) := by
  change (floor (alpha*N)).value = _
  exact floor_value _ (by positivity)

theorem floorSearch_operations_le (N : ℕ) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    (floorSearch N alpha).operations ≤ 2*N+2 := by
  have h := floor_alpha_operations N ha ha1
  dsimp [floorSearch]
  omega

open AlgorithmBudgets

/-- The edge cutoff is computed with the same division/logarithm argument as in
the analysis, followed by a genuine integer search. -/
def edgeSearch (q Lambda : ℝ) : Result :=
  let r := ceiling (Lambda / Real.log (1/q))
  ⟨r.value,r.operations+3⟩

/-- Two real operations form the exponential argument before the search. -/
def repetitionSearch (L : ℕ) (Lambda : ℝ) : Result :=
  let r := ceiling (Real.exp ((L:ℝ)+Lambda))
  ⟨r.value,r.operations+2⟩

@[simp] theorem edgeSearch_value (q Lambda : ℝ) :
    (edgeSearch q Lambda).value = edgeCutoff q Lambda := by
  simp [edgeSearch, edgeCutoff]

@[simp] theorem edgeSearch_operations (q Lambda : ℝ) :
    (edgeSearch q Lambda).operations = 2*edgeCutoff q Lambda+4 := by
  simp [edgeSearch, edgeCutoff]

@[simp] theorem repetitionSearch_value (L : ℕ) (Lambda : ℝ) :
    (repetitionSearch L Lambda).value = colorTrials L Lambda := by
  simp [repetitionSearch, colorTrials]

@[simp] theorem repetitionSearch_operations (L : ℕ) (Lambda : ℝ) :
    (repetitionSearch L Lambda).operations = 2*colorTrials L Lambda+3 := by
  simp [repetitionSearch, colorTrials]

/-- All variable integer cutoffs together cost only linear work in `N+L+R`. -/
theorem all_rounding_operations (N : ℕ) {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (q Lambda : ℝ) :
    (floorSearch N alpha).operations + (edgeSearch q Lambda).operations +
      (repetitionSearch (edgeCutoff q Lambda) Lambda).operations ≤
        10*(N + edgeCutoff q Lambda + colorTrials (edgeCutoff q Lambda) Lambda + 1) := by
  have hf := floorSearch_operations_le N ha ha1
  rw [edgeSearch_operations, repetitionSearch_operations]
  omega

end SpinGlass.RoundingExecution
