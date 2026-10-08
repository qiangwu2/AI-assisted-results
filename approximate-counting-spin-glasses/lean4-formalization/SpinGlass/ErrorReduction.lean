import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Deterministic error reduction

This file proves the deterministic logarithmic-accuracy step in the paper.
It does not assume the paper's lower-tail or mean-square estimates.
-/

namespace SpinGlass

/-- The paper's output is defined on every real correction, including nonpositive ones. -/
noncomputable def logOutput (base correction : ℝ) : ℝ :=
  base + if 0 < correction then Real.log correction else 0

/-- A relative error at most ε/2, for ε ≤ 1, controls log error by ε. -/
theorem log_error_of_relative {t z ε : ℝ}
    (hz : 0 < z) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herror : |t - z| ≤ ε * z / 2) :
    0 < t ∧ |Real.log t - Real.log z| ≤ ε := by
  have hlower : -(ε * z / 2) ≤ t - z := (abs_le.mp herror).1
  have hupper : t - z ≤ ε * z / 2 := (abs_le.mp herror).2
  have ht : 0 < t := by nlinarith
  have htz : 0 < t / z := div_pos ht hz
  have hzt : 0 < z / t := div_pos hz ht
  have hlogupper := Real.log_le_sub_one_of_pos htz
  have hloglower := Real.log_le_sub_one_of_pos hzt
  have hratioUpper : t / z ≤ 1 + ε := by
    apply (div_le_iff₀ hz).2
    nlinarith
  have htHalf : z / 2 ≤ t := by nlinarith
  have hmul := mul_nonneg (le_of_lt hε) (sub_nonneg.mpr htHalf)
  have hratioLower : z / t ≤ 1 + ε := by
    apply (div_le_iff₀ ht).2
    nlinarith
  refine ⟨ht, abs_le.mpr ⟨?_, ?_⟩⟩
  · rw [Real.log_div (ne_of_gt hz) (ne_of_gt ht)] at hloglower
    linarith
  · rw [Real.log_div (ne_of_gt ht) (ne_of_gt hz)] at hlogupper
    linarith

/-- The paper uses an absolute error scaled by a deterministic lower threshold. -/
theorem log_error_of_absolute {t z threshold ε : ℝ}
    (hthreshold : 0 < threshold) (hz : threshold ≤ z)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herror : |t - z| ≤ ε * threshold / 2) :
    0 < t ∧ |Real.log t - Real.log z| ≤ ε := by
  apply log_error_of_relative (lt_of_lt_of_le hthreshold hz) hε hε1
  calc
    |t - z| ≤ ε * threshold / 2 := herror
    _ ≤ ε * z / 2 := by gcongr

/-- On the success event, the total output has the desired additive accuracy. -/
theorem logOutput_error {base t z threshold ε : ℝ}
    (hthreshold : 0 < threshold) (hz : threshold ≤ z)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herror : |t - z| ≤ ε * threshold / 2) :
    |logOutput base t - (base + Real.log z)| ≤ ε := by
  obtain ⟨ht, hlog⟩ := log_error_of_absolute hthreshold hz hε hε1 herror
  simpa [logOutput, ht] using hlog

/-- The bad output event is contained in the union of the two events bounded by the paper. -/
theorem logOutput_bad_event_subset {Ω : Type*} (base T Z : Ω → ℝ)
    {threshold ε : ℝ} (hthreshold : 0 < threshold)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    {ω | ε < |logOutput (base ω) (T ω) - (base ω + Real.log (Z ω))|} ⊆
      {ω | Z ω < threshold} ∪ {ω | ε * threshold / 2 < |T ω - Z ω|} := by
  intro ω hbad
  by_cases hz : Z ω < threshold
  · exact Or.inl hz
  · right
    by_contra herr
    have hgood := logOutput_error (base := base ω) hthreshold (le_of_not_gt hz)
      hε hε1 (le_of_not_gt herr)
    exact (not_lt_of_ge hgood) hbad


open MeasureTheory

/-- Chebyshev's estimate for an arbitrary square-integrable real error. -/
theorem abs_error_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Ω → ℝ)
    (hE : Integrable (fun ω => (E ω) ^ 2) μ)
    {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a < |E ω|} ≤ (∫ ω, (E ω) ^ 2 ∂μ) / a ^ 2 := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => (E ω) ^ 2)
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (E ω))) hE (a ^ 2)
  have hsubset : {ω | a < |E ω|} ⊆ {ω | a ^ 2 ≤ (E ω) ^ 2} := by
    intro ω hω
    have hsq := sq_abs (E ω)
    have habs := abs_nonneg (E ω)
    dsimp at hω ⊢
    nlinarith
  have hprob := measureReal_mono (μ := μ) hsubset
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  calc
    μ.real {ω | a < |E ω|} * a ^ 2 ≤
        μ.real {ω | a ^ 2 ≤ (E ω) ^ 2} * a ^ 2 :=
      mul_le_mul_of_nonneg_right hprob (sq_nonneg a)
    _ ≤ ∫ ω, (E ω) ^ 2 ∂μ := by simpa [mul_comm] using hmarkov

/-- The paper's failure bound before substituting the lower-tail and MSE estimates.
No independence between the correction and partition function is required. -/
theorem logOutput_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (base T Z : Ω → ℝ)
    (hE : Integrable (fun ω => (T ω - Z ω) ^ 2) μ)
    {threshold ε : ℝ} (hthreshold : 0 < threshold)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    μ.real {ω | ε < |logOutput (base ω) (T ω) - (base ω + Real.log (Z ω))|} ≤
      μ.real {ω | Z ω < threshold} +
        4 * (∫ ω, (T ω - Z ω) ^ 2 ∂μ) / (ε ^ 2 * threshold ^ 2) := by
  have ha : 0 < ε * threshold / 2 := by positivity
  have hmarkov := abs_error_probability μ (fun ω => T ω - Z ω) hE ha
  have hscale : (∫ ω, (T ω - Z ω) ^ 2 ∂μ) / (ε * threshold / 2) ^ 2 =
      4 * (∫ ω, (T ω - Z ω) ^ 2 ∂μ) / (ε ^ 2 * threshold ^ 2) := by ring
  rw [hscale] at hmarkov
  exact (measureReal_mono (logOutput_bad_event_subset base T Z hthreshold hε hε1)).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl hmarkov))

/-- Substitution of the paper's two probability budgets.
The upstream lower-tail and mean-square estimates remain explicit hypotheses. -/
theorem logOutput_probability_of_budgets {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (base T Z : Ω → ℝ)
    (hE : Integrable (fun ω => (T ω - Z ω) ^ 2) μ)
    {threshold ε δ τ : ℝ} (hthreshold : 0 < threshold)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlower : μ.real {ω | Z ω < threshold} ≤ τ + δ / 2)
    (hmse : (∫ ω, (T ω - Z ω) ^ 2 ∂μ) ≤ δ * ε ^ 2 * threshold ^ 2 / 8) :
    μ.real {ω | ε < |logOutput (base ω) (T ω) - (base ω + Real.log (Z ω))|} ≤
      τ + δ := by
  have hden : 0 < ε ^ 2 * threshold ^ 2 := by positivity
  have hbound : 4 * (∫ ω, (T ω - Z ω) ^ 2 ∂μ) / (ε ^ 2 * threshold ^ 2) ≤ δ / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  exact (logOutput_probability μ base T Z hE hthreshold hε hε1).trans (by linarith)

end SpinGlass

