import SpinGlass.DisorderModel
import SpinGlass.TanhBound

/-! # The variance-one disorder bound for the true tanh edge weights -/
noncomputable section
namespace SpinGlass.Disorder
open MeasureTheory

/-- The manuscript's variance-one assumption implies the required upper bound
on the true single-edge second moment, with no higher moment assumption. -/
theorem secondMoment_le_scale_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) (a : ℝ) : secondMoment μ a ≤ a ^ 2 := by
  calc
    secondMoment μ a ≤ ∫ x : ℝ, a ^ 2 * x ^ 2 ∂μ := by
      apply integral_mono (integrable_weight_sq μ a) (hunit.integrable_sq.const_mul _)
      intro x
      simpa only [weight, mul_pow] using SpinGlass.TanhBound.tanh_sq_le_sq (a * x)
    _ = a ^ 2 := by rw [integral_const_mul, hunit.integral_sq, mul_one]

end SpinGlass.Disorder
