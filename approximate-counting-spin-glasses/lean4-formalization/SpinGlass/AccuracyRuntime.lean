import SpinGlass.CountingReduction
import SpinGlass.PolynomialRuntime

/-! Exact conversion from the selected MSE budget to polynomial dependence
on logarithmic accuracy and confidence. -/

noncomputable section
namespace SpinGlass.AccuracyRuntime
open Real

theorem log_accuracyMSEBudget {C delta epsilon s : ℝ}
    (hC : 0 < C) (hd : 0 < delta) (he : 0 < epsilon) :
    Real.log (SpinGlass.accuracyMSEBudget C delta epsilon s) =
      (1+2/s)*Real.log delta + 2*Real.log epsilon -
        (Real.log 8 + (2/s)*Real.log (2*C)) := by
  have hz := SpinGlass.accuracyThreshold_pos (s := s) hC hd
  have hr : 0 < delta/(2*C) := by positivity
  unfold SpinGlass.accuracyMSEBudget
  rw [Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) (pow_pos hz 2).ne',
    Real.log_mul hd.ne' (pow_pos he 2).ne', Real.log_pow, Real.log_pow]
  unfold SpinGlass.accuracyThreshold
  rw [Real.log_rpow hr, Real.log_div hd.ne' (by positivity)]
  ring

def budgetFactor (C s k : ℝ) : ℝ :=
  Real.exp (k*(Real.log 8 + (2/s)*Real.log (2*C)))

theorem inverse_budget_identity {C delta epsilon s k : ℝ}
    (hC : 0 < C) (hd : 0 < delta) (he : 0 < epsilon) :
    (SpinGlass.accuracyMSEBudget C delta epsilon s)^(-k) =
      budgetFactor C s k * epsilon^(-(2*k)) * delta^(-((1+2/s)*k)) := by
  have hu := SpinGlass.accuracyMSEBudget_pos (s := s) hC hd he
  rw [Real.rpow_def_of_pos hu, log_accuracyMSEBudget hC hd he,
    Real.rpow_def_of_pos he, Real.rpow_def_of_pos hd, budgetFactor,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

def countingConstant (A C s k : ℝ) : ℝ :=
  max 1 (max k (max (2*k) (max ((1+2/s)*k) (A*budgetFactor C s k))))

theorem countingConstant_pos (A C s k : ℝ) : 0 < countingConstant A C s k :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- A mean-square polynomial bound yields precisely the common-exponent
accuracy/confidence polynomial in the main theorem. -/
theorem budget_polynomial {A C s k delta epsilon : ℝ} {N : ℕ}
    (hA : 0 ≤ A) (hC : 0 < C) (hN : 1 ≤ N)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    A*(N:ℝ)^k*(SpinGlass.accuracyMSEBudget C delta epsilon s)^(-k) ≤
      countingConstant A C s k * (N:ℝ)^(countingConstant A C s k) *
        epsilon^(-countingConstant A C s k) * delta^(-countingConstant A C s k) := by
  let D := countingConstant A C s k
  have hD0 : 0 < D := countingConstant_pos _ _ _ _
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hk : k ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have heK : 2*k ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hdK : (1+2/s)*k ≤ D :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hcoef : A*budgetFactor C s k ≤ D :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hnPow := Real.rpow_le_rpow_of_exponent_le hN1 hk
  have hePow := Real.rpow_le_rpow_of_exponent_ge he he1 (neg_le_neg heK)
  have hdPow := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hdK)
  rw [inverse_budget_identity hC hd he]
  calc
    _ = (A*budgetFactor C s k)*(N:ℝ)^k*epsilon^(-(2*k))*delta^(-((1+2/s)*k)) := by ring
    _ ≤ _ := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul hcoef hnPow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hD0.le
        · exact hePow
        · exact (Real.rpow_pos_of_pos he _).le
        · exact mul_nonneg hD0.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact hdPow
      · exact (Real.rpow_pos_of_pos hd _).le
      · exact mul_nonneg (mul_nonneg hD0.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_pos_of_pos he _).le

end SpinGlass.AccuracyRuntime
