import SpinGlass.SKUniformAlgorithm
import SpinGlass.CountingReduction

/-! Logarithmic probability guarantee for the automatic SK graph-sum estimator.
The equality to the fast evaluator is a separate implementation theorem. -/
noncomputable section
namespace SpinGlass.SKCounting
open MeasureTheory
open SpinGlass.Disorder SpinGlass.DesignConstants SpinGlass.CountingReduction

/-- A disorder-only event has exactly the same probability after independent
algorithm randomness is added to the sample space. -/
theorem disorder_event_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E : Type*} [Fintype E] (S : Set (E → ℝ)) :
    (P.prod (iidLaw μ)).real {ωJ : Ω × (E → ℝ) | ωJ.2 ∈ S} = (iidLaw μ).real S := by
  have heq : {ωJ : Ω × (E → ℝ) | ωJ.2 ∈ S} = Set.univ ×ˢ S := by ext x; simp
  rw [heq, measureReal_prod_prod]
  simp [Measure.real]

/-- The paper's lower-tail/log reduction on the genuine independent product
space; only the algorithm MSE and its integrability are generic inputs. -/
theorem probability_of_joint_mse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N : ℕ} (hN : 2 ≤ N) {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1)
    (T : Ω → (Finset (Fin N) → ℝ) → ℝ)
    (hE : Integrable (fun ωJ : Ω × (Finset (Fin N) → ℝ) =>
      (T ωJ.1 ωJ.2 - normalized 2 N beta ωJ.2) ^ 2) (P.prod (iidLaw μ)))
    (hmse : (∫ ωJ : Ω × (Finset (Fin N) → ℝ),
      (T ωJ.1 ωJ.2 - normalized 2 N beta ωJ.2) ^ 2 ∂P.prod (iidLaw μ)) ≤
        mseBudget 2 B epsilon delta) :
    (P.prod (iidLaw μ)).real {ωJ : Ω × (Finset (Fin N) → ℝ) |
      epsilon < |SpinGlass.logOutput (logBase 2 N beta ωJ.2) (T ωJ.1 ωJ.2) -
        targetLog 2 N beta ωJ.2|} ≤ remainder μ 2 N B + delta := by
  have hC := constant_ge_one hB hBT
  have hC0 : 0 < constant 2 B := by linarith
  have hs := exponent_pos hB hBT
  have hz := SpinGlass.accuracyThreshold_pos (s := exponent 2 B) hC0 hd
  have hz1 := SpinGlass.accuracyThreshold_lt_one hC hd hd1 hs
  have hplus := inflatedBeta_admissible hB hBT
  have htail := pure_p_spin_lower_tail_uniform_temperature μ hμ hunit (by omega : 0 < 2) hN
    hbeta hbetaB hB hplus.1 hplus.2 hz hz1.le
  simp_rw [targetLog_decomposition]
  apply SpinGlass.logOutput_probability_with_paper_parameters (P.prod (iidLaw μ))
    (fun ωJ : Ω × (Finset (Fin N) → ℝ) => logBase 2 N beta ωJ.2)
    (fun ωJ => T ωJ.1 ωJ.2) (fun ωJ => normalized 2 N beta ωJ.2)
    hE hC0 hd he he1.le hs _ hmse
  have hp := disorder_event_probability P μ
    {J : Finset (Fin N) → ℝ | normalized 2 N beta J < SpinGlass.accuracyThreshold (constant 2 B) delta (exponent 2 B)}
  simp only [Set.mem_setOf_eq] at hp
  rw [hp]
  simpa only [normalized, constant, exponent, theta, remainder, add_comm] using htail

end SpinGlass.SKCounting

namespace SpinGlass.SKUniformAlgorithm
open MeasureTheory
open SpinGlass.Disorder SpinGlass.DesignConstants SpinGlass.CountingReduction

/-- The requested log partition estimate from the automatic graph-sum semantics. -/
def count (N : ℕ) (B beta epsilon delta : ℝ)
    (χ : Randomness N B (mseBudget 2 B epsilon delta)) (J : Finset (Fin N) → ℝ) : ℝ :=
  SpinGlass.logOutput (logBase 2 N beta J) (run N B beta (mseBudget 2 B epsilon delta) χ J)

/-- Final δ+τ guarantee for the original real-disorder law and independent
actual color trials. The fast evaluator will inherit this by exact value equality. -/
theorem counting_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N : ℕ} (hN : 2 ≤ N)
    {B beta epsilon delta : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    ((randomLaw N B (mseBudget 2 B epsilon delta)).prod (iidLaw μ)).real
      {χJ : Randomness N B (mseBudget 2 B epsilon delta) × (Finset (Fin N) → ℝ) |
        epsilon < |count N B beta epsilon delta χJ.1 χJ.2 - targetLog 2 N beta χJ.2|} ≤
      remainder μ 2 N B + delta := by
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  letI := randomLaw_probability (N := N) hB hBT hu.1 hu.2
  apply SpinGlass.SKCounting.probability_of_joint_mse (randomLaw N B (mseBudget 2 B epsilon delta))
    μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1 (run N B beta (mseBudget 2 B epsilon delta))
  · simpa only [normalized, sub_sq_comm] using error_integrable μ hB hBT hu.1 hu.2
  · simpa only [normalized, sub_sq_comm] using mean_square μ hμ hunit hN hB hBT hbeta hbetaB hu.1 hu.2

end SpinGlass.SKUniformAlgorithm
