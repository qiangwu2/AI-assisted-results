import SpinGlass.SupportScalar
import SpinGlass.SKBranchingPairings

/-! Finite coefficient bounds for the branching-degree generating polynomial. -/
noncomputable section
namespace SpinGlass.SKBranching
open scoped BigOperators Nat
open Finset Real

/-- The factorial coefficient comparison used for every even degree at least four. -/
theorem branching_factorial_lower (j : ℕ) :
    24 * 2 ^ j * j.factorial ≤ (2 * j + 4).factorial := by
  have hdouble := Nat.doubleFactorial_le_factorial (2 * j)
  rw [Nat.doubleFactorial_two_mul] at hdouble
  have hprod : (2 * j).factorial * (4 : ℕ).factorial ≤ (2 * j + 4).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  apply (show 24 * 2 ^ j * j.factorial ≤ (2 * j).factorial * (4 : ℕ).factorial from ?_).trans hprod
  norm_num
  nlinarith

/-- Every finite sum of the high even-degree terms is dominated by the
explicit fourth-power times Gaussian-exponential factor. No infinite-series
interchange is required for this finite version. -/
theorem finite_branching_series_le (x : ℝ) (K : ℕ) :
    (∑ j ∈ Finset.range K, x ^ (2 * j + 4) / (2 * j + 4).factorial) ≤
      x ^ 4 / 24 * Real.exp (x ^ 2 / 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range K, x ^ 4 / 24 * ((x ^ 2 / 2) ^ j / j.factorial) := by
      apply Finset.sum_le_sum
      intro j hj
      have hfac : (24 : ℝ) * 2 ^ j * (j.factorial : ℝ) ≤ (2 * j + 4).factorial := by
        exact_mod_cast branching_factorial_lower j
      have hden : 0 < (24 : ℝ) * 2 ^ j * (j.factorial : ℝ) := by positivity
      calc
        _ ≤ x ^ (2 * j + 4) / ((24 : ℝ) * 2 ^ j * (j.factorial : ℝ)) :=
          div_le_div_of_nonneg_left (by rw [pow_add, pow_mul]; positivity) hden hfac
        _ = _ := by rw [pow_add, pow_mul, div_pow]; ring
    _ = x ^ 4 / 24 * ∑ j ∈ Finset.range K, (x ^ 2 / 2) ^ j / j.factorial := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) K) (by positivity)

/-- The outside-branch degree-zero-or-two factor has its exact exponential bound. -/
theorem nonbranch_factor_le (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.exp (x ^ 2 / 2) := by
  simpa only [add_comm] using Real.add_one_le_exp (x ^ 2 / 2)

end SpinGlass.SKBranching
