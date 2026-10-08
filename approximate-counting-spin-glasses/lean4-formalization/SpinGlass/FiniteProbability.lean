import SpinGlass.ColoringProbability
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Actual probability measures for the finite color sample spaces. -/

noncomputable section
namespace SpinGlass.FiniteProbability
open MeasureTheory
open scoped ENNReal BigOperators

variable (Ω : Type*) [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

def uniformLaw : Measure Ω := ((Fintype.card Ω : ℝ≥0∞)⁻¹) • Measure.count

instance [Nonempty Ω] : IsProbabilityMeasure (uniformLaw Ω) := by
  constructor
  simp [uniformLaw, ENNReal.inv_mul_cancel, Fintype.card_ne_zero]

theorem integral_uniformLaw (f : Ω → ℝ) :
    (∫ x, f x ∂uniformLaw Ω) = SpinGlass.ColoringProbability.mean f := by
  simp [uniformLaw, integral_smul_measure, integral_count, SpinGlass.ColoringProbability.mean]

end SpinGlass.FiniteProbability
