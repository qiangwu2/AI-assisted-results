import SpinGlass.SKFastEvaluator

/-!
# Explicit arithmetic accounting for the scheduled SK evaluator

Counts charge all cardinality passes, all possible predecessors and closures,
all dense basis pairs, scaling, additions, and extraction. They deliberately
include invalid states and rejected basis pairs, so no favorable sparsity is
needed. The exponent of the ambient size is absolute.
-/

namespace SpinGlass.SKOperationCount

/-- Coefficient-register count. -/
def registers (b L : ℕ) : ℕ := (L + 1) * 2 ^ L * 6 ^ b

/-- All branch and outside-root table passes, with multiply/accumulate costs. -/
def tableWork (N b L : ℕ) : ℕ := (b + N) * (2 * L * 2 ^ L * N ^ 2)

/-- Closures, normalizations, and accumulation into the primitive array. -/
def closureWork (N b L : ℕ) : ℕ :=
  2 * 2 ^ L * (b ^ 2 * N + b * N + N ^ 2) +
    2 ^ L * (b + 1) + 2 ^ L * (b ^ 2 + b + 1)

/-- Exponential/direct products, scaling, additions, and extraction. -/
def algebraWork (b L : ℕ) : ℕ :=
  (L + b ^ 2) * (2 * registers b L ^ 2 + 2 * registers b L + 1) +
    2 * registers b L

/-- A uniform arithmetic schedule upper bound for one full colorful evaluation. -/
def trialWork (N b L : ℕ) : ℕ := tableWork N b L + closureWork N b L + algebraWork b L

/-- A branch-pair schedule never exceeds the claimed quadratic count. -/
theorem directPairs_card_le (b : ℕ) : (SKFastEvaluator.directPairs b).card ≤ b ^ 2 := by
  calc
    _ ≤ (Finset.univ : Finset (Fin b × Fin b)).card := Finset.card_filter_le _ _
    _ = b ^ 2 := by simp [pow_two]

/-- Squared register count is the exact multiplication factor. -/
theorem registers_sq (b L : ℕ) : registers b L ^ 2 = (L + 1) ^ 2 * 4 ^ L * 36 ^ b := by
  have h4 : (4 : ℕ) ^ L = (2 ^ L) ^ 2 := by
    rw [← Nat.pow_mul, Nat.mul_comm L 2, Nat.pow_mul]
  have h36 : (36 : ℕ) ^ b = (6 ^ b) ^ 2 := by
    rw [← Nat.pow_mul, Nat.mul_comm b 2, Nat.pow_mul]
  rw [registers, h4, h36]
  ring

/-- Every explicit work contribution is bounded by one absolute polynomial times
`4^L 36^b`; neither the exponent nor the constant depends on any cutoff. -/
theorem trialWork_bound (N b L : ℕ) (hb : b ≤ N) :
    trialWork N b L ≤ 32 * (N + L + 1) ^ 4 * 4 ^ L * 36 ^ b := by
  let M := N + L + 1
  let T := 4 ^ L * 36 ^ b
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hN : N ≤ M := by dsimp [M]; omega
  have hbM : b ≤ M := le_trans hb hN
  have hL : L ≤ M := by dsimp [M]; omega
  have hL1 : L + 1 ≤ M := by dsimp [M]; omega
  have hT : 1 ≤ T := Nat.succ_le_of_lt (by dsimp [T]; positivity)
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith [sq_nonneg (M - 1 : ℤ)]
  have hM4 : M ^ 3 ≤ M ^ 4 := by nlinarith [Nat.mul_le_mul_left (M ^ 2) hM2]
  have h24 : M ^ 2 ≤ M ^ 4 := le_trans hM3 hM4
  have h2 : 2 ^ L ≤ T := by
    calc
      2 ^ L ≤ 4 ^ L := Nat.pow_le_pow_left (by omega) _
      _ ≤ 4 ^ L * 36 ^ b := Nat.le_mul_of_pos_right _ (by positivity)
  have hreg2 : registers b L ^ 2 ≤ M ^ 2 * T := by
    rw [registers_sq]
    dsimp [T]
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (36 ^ b) (Nat.mul_le_mul_right (4 ^ L) (Nat.pow_le_pow_left hL1 2))
  have hregpos : 1 ≤ registers b L := Nat.succ_le_of_lt (by unfold registers; positivity)
  have hreg : registers b L ≤ M ^ 2 * T := by
    have : registers b L ≤ registers b L ^ 2 := by nlinarith
    exact le_trans this hreg2
  have htable : tableWork N b L ≤ 4 * M ^ 4 * T := by
    unfold tableWork
    calc
      (b + N) * (2 * L * 2 ^ L * N ^ 2) ≤
          (M + M) * (2 * M * T * M ^ 2) := by gcongr
      _ = 4 * M ^ 4 * T := by ring
  have hclose : closureWork N b L ≤ 11 * M ^ 4 * T := by
    unfold closureWork
    calc
      _ ≤ 2 * T * (M ^ 2 * M + M * M + M ^ 2) +
          T * (M + 1) + T * (M ^ 2 + M + 1) := by gcongr
      _ ≤ 11 * M ^ 4 * T := by
        nlinarith [Nat.mul_le_mul_right T hM, Nat.mul_le_mul_right T hM2,
          Nat.mul_le_mul_right T hM3, Nat.mul_le_mul_right T hM4,
          Nat.mul_le_mul_right T h24]
  have halg : algebraWork b L ≤ 12 * M ^ 4 * T := by
    unfold algebraWork
    calc
      _ ≤ (M + M ^ 2) * (2 * (M ^ 2 * T) + 2 * (M ^ 2 * T) + 1) +
          2 * (M ^ 2 * T) := by gcongr
      _ ≤ (2 * M ^ 2) * (5 * (M ^ 2 * T)) + 2 * (M ^ 2 * T) := by
        gcongr <;> nlinarith
      _ ≤ 12 * M ^ 4 * T := by nlinarith [Nat.mul_le_mul_right T h24]
  unfold trialWork
  change _ ≤ 32 * M ^ 4 * 4 ^ L * 36 ^ b
  have ht : 32 * M ^ 4 * 4 ^ L * 36 ^ b = 32 * M ^ 4 * T := by dsimp [T]; ring
  rw [ht]
  nlinarith

end SpinGlass.SKOperationCount
