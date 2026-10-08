import SpinGlass.HigherOrderRuntime
import SpinGlass.CountingReduction
import SpinGlass.PolynomialIntegrability

/-! The final logarithmic counting guarantee for the actual higher-order algorithm. -/

noncomputable section
namespace SpinGlass.HigherOrderAlgorithm
open MeasureTheory Finset
open SpinGlass.Disorder SpinGlass.DesignConstants SpinGlass.CountingReduction
open SpinGlass.SupportEvaluation SpinGlass.SupportMeanSquare

def count (p N : ℕ) (B beta epsilon delta : ℝ) (J : Finset (Fin N) → ℝ) : ℝ :=
  SpinGlass.logOutput (logBase p N beta J)
    (run p N B beta (mseBudget p B epsilon delta) J).value

theorem error_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p N : ℕ) (B beta u : ℝ) :
    Integrable (fun J : Finset (Fin N) → ℝ =>
      ((run p N B beta u J).value - normalized p N beta J)^2) (iidLaw μ) := by
  classical
  by_cases he : exactBranch p N B u
  · simpa only [run, if_pos he, exactEvaluator_disorder_value, normalized, sub_self,
      zero_pow (by norm_num : 2 ≠ 0)] using (integrable_const (0 : ℝ) :
        Integrable (fun _ : Finset (Fin N) → ℝ => (0 : ℝ)) (iidLaw μ))
  · have hfull (J : Finset (Fin N) → ℝ) : normalized p N beta J =
        ∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs p : Finset (Finset (Finset (Fin N)))),
          monomial (fun _ => pureScale N p beta) Γ J := by
      rw [normalized, SpinGlass.Partition.normalizedPartition_eq_even_sum]
      rfl
    simp_rw [run, if_neg he, higherEvaluator_disorder_value, hfull, supportApproximation]
    simpa only [one_mul] using SpinGlass.PolynomialIntegrability.integrable_difference_square μ
      (fun _ : Finset (Fin N) => pureScale N p beta) _ _ (fun _ => 1) (fun _ => 1)

/-- For every finite input size, every temperature in the full admitted range,
and every requested accuracy/confidence, the actual algorithm has the paper's
failure probability. No probabilistic or algorithmic lemma is assumed. -/
theorem counting_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {p N : ℕ} (hp : 3 ≤ p) (hpN : p ≤ N)
    {B beta epsilon delta : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    (iidLaw μ).real {J : Finset (Fin N) → ℝ |
      epsilon < |count p N B beta epsilon delta J - targetLog p N beta J|} ≤ remainder μ p N B + delta := by
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  exact probability_of_mse μ hμ hunit (by omega) hpN hB hBT hbeta hbetaB he he1 hd hd1
    (fun J => (run p N B beta (mseBudget p B epsilon delta) J).value)
    (error_integrable μ _ _ _ _ _) (mean_square μ hμ hunit hp hpN hB hBT hbeta hbetaB hu.1 hu.2)

end SpinGlass.HigherOrderAlgorithm
