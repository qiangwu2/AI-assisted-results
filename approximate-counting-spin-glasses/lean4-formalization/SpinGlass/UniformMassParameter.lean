import SpinGlass.UniformMassEntropy
import Mathlib.Data.Nat.Factorial.Basic

/-! Coefficient restrictions needed for the uniform graphical-mass product comparison. -/

namespace SpinGlass.UniformMassParameter

open SpinGlass.UniformMassEntropy

theorem factorial_succ_le_pow (k : ℕ) : (k + 1).factorial ≤ (k + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (k + 1 + 1).factorial = (k + 2) * (k + 1).factorial := by rw [Nat.factorial_succ]
      _ ≤ (k + 2) * (k + 1) ^ k := Nat.mul_le_mul_left _ ih
      _ ≤ (k + 2) * (k + 2) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (k + 1 + 1) ^ (k + 1) := by simp only [Nat.pow_succ, Nat.add_assoc, Nat.reduceAdd, Nat.mul_comm]

theorem factorial_le_pow_pred {p : ℕ} (hp : 1 ≤ p) : p.factorial ≤ p ^ (p - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  simpa using factorial_succ_le_pow k

theorem thresholdSquared_lt_pow_pred {p : ℕ} (hp : 1 ≤ p) :
    thresholdSquared p < (p : ℝ) ^ (p - 1) := by
  have hf : (p.factorial : ℝ) ≤ (p : ℝ) ^ (p - 1) := by
    exact_mod_cast factorial_le_pow_pred hp
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  have hfact : 0 < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  exact (thresholdSquared_le_factorial_log_two p).trans_lt
    ((by nlinarith : (p.factorial : ℝ) * Real.log 2 < p.factorial).trans_le hf)

/-- The actual inflated mass coefficient is in `[0,1)` throughout the stated
temperature range, including the smallest permitted system size. -/
theorem mass_coefficient_range {N p : ℕ} (hp : 1 ≤ p) (hNp : p ≤ N)
    {v : ℝ} (hv : 0 ≤ v) (hvt : v < thresholdSquared p) :
    0 ≤ v / (N : ℝ) ^ (p - 1) ∧ v / (N : ℝ) ^ (p - 1) < 1 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hpow : (p : ℝ) ^ (p - 1) ≤ (N : ℝ) ^ (p - 1) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hNp) _
  refine ⟨div_nonneg hv (pow_nonneg hN.le _), ?_⟩
  apply (div_lt_one (pow_pos hN _)).2
  exact hvt.trans ((thresholdSquared_lt_pow_pred hp).trans_le hpow)

end SpinGlass.UniformMassParameter
