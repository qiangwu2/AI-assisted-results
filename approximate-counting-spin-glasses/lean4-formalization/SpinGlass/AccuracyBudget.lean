import SpinGlass.ErrorReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

/-!
# The paper's final choice of accuracy budgets

This proves the parameter substitution, including membership of the MSE budget
in (0,1). It is a conditional reduction: the lower-tail and MSE inequalities
are hypotheses, not assertions about an implemented algorithm.
-/

namespace SpinGlass
open MeasureTheory

noncomputable def accuracyThreshold (C δ s : ℝ) : ℝ := (δ / (2 * C)) ^ (1 / s)
noncomputable def accuracyMSEBudget (C δ ε s : ℝ) : ℝ :=
  δ * ε ^ 2 * (accuracyThreshold C δ s) ^ 2 / 8

theorem accuracyThreshold_pos {C δ s : ℝ} (hC : 0 < C) (hδ : 0 < δ) :
    0 < accuracyThreshold C δ s := by
  exact Real.rpow_pos_of_pos (div_pos hδ (by positivity)) _

theorem accuracyThreshold_rpow {C δ s : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hs : 0 < s) :
    (accuracyThreshold C δ s) ^ s = δ / (2 * C) := by
  unfold accuracyThreshold
  rw [← Real.rpow_mul (le_of_lt (div_pos hδ (by positivity)))]
  rw [one_div_mul_cancel (ne_of_gt hs), Real.rpow_one]

theorem accuracyThreshold_lt_one {C δ s : ℝ}
    (hC : 1 ≤ C) (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) :
    accuracyThreshold C δ s < 1 := by
  have hden : 0 < 2 * C := by linarith
  apply Real.rpow_lt_one (le_of_lt (div_pos hδ hden))
  · apply (div_lt_iff₀ hden).2
    linarith
  · positivity

theorem accuracyMSEBudget_pos {C δ ε s : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hε : 0 < ε) :
    0 < accuracyMSEBudget C δ ε s := by
  unfold accuracyMSEBudget
  have hz := accuracyThreshold_pos (s := s) hC hδ
  positivity

theorem accuracyMSEBudget_lt_one {C δ ε s : ℝ}
    (hC : 1 ≤ C) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < s) :
    accuracyMSEBudget C δ ε s < 1 := by
  have hz := accuracyThreshold_pos (s := s) (by linarith : 0 < C) hδ
  have hz1 := accuracyThreshold_lt_one hC hδ hδ1 hs
  have he2 : ε ^ 2 < 1 := by nlinarith
  have hz2 : (accuracyThreshold C δ s) ^ 2 < 1 := by nlinarith
  unfold accuracyMSEBudget
  calc
    δ * ε ^ 2 * accuracyThreshold C δ s ^ 2 / 8 < 1 * 1 * 1 / 8 := by
      gcongr
    _ < 1 := by norm_num

/-- If the two upstream estimates hold at the chosen parameters, failure is at most τ+δ. -/
theorem logOutput_probability_with_paper_parameters
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (base T Z : Ω → ℝ)
    (hE : Integrable (fun ω => (T ω - Z ω) ^ 2) μ)
    {C δ ε s τ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 < s)
    (hlower : μ.real {ω | Z ω < accuracyThreshold C δ s} ≤
      τ + C * accuracyThreshold C δ s ^ s)
    (hmse : (∫ ω, (T ω - Z ω) ^ 2 ∂μ) ≤ accuracyMSEBudget C δ ε s) :
    μ.real {ω | ε < |logOutput (base ω) (T ω) - (base ω + Real.log (Z ω))|} ≤ τ + δ := by
  apply logOutput_probability_of_budgets μ base T Z hE
    (accuracyThreshold_pos hC hδ) hε hε1
  · rw [accuracyThreshold_rpow hC hδ hs] at hlower
    have hc : C * (δ / (2 * C)) = δ / 2 := by field_simp
    simpa [hc] using hlower
  · exact hmse

end SpinGlass
