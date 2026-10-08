import SpinGlass.SKCoefficientCorrectness
import SpinGlass.SKCounting
import SpinGlass.InputPreparation

/-! # Full correctness of the actual SK evaluator under the original disorder law -/
noncomputable section
namespace SpinGlass.SKUniformAlgorithm
open MeasureTheory
open SpinGlass.Disorder SpinGlass.DesignConstants SpinGlass.CountingReduction

/-- The implemented correction uses exact spin enumeration or the verified
color-subset evaluator according to the actual automatic branch test. -/
def fastRun (N : ℕ) (B beta u : ℝ) (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) : ℝ := by
  classical
  exact if exactBranch N B u then
    (SpinGlass.SupportEvaluation.exactEvaluator 2 (fun e => weight (pureScale N 2 beta) (J e))).value
  else SpinGlass.SKActualEvaluator.estimator (selectedSize N B u - 1)
    (edgeLimit B u) (repetitions B u) χ (fun e => weight (pureScale N 2 beta) (J e))

/-- Every literal implementation step agrees with the analyzed graph-sum output. -/
theorem fastRun_eq_run {N : ℕ} {B beta u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    fastRun N B beta u χ J = run N B beta u χ J := by
  classical
  unfold fastRun run
  split_ifs
  · exact SpinGlass.SupportEvaluation.exactEvaluator_disorder_value 2 _ J
  · exact SpinGlass.SKCoefficientCorrectness.estimator_eq_disorder _ _ _
      (edgeLimit_pos hB hBT hu hu1) χ _ J

/-- No unproved evaluator identity or mass bound remains in the implemented
algorithm's mean-square theorem. -/
theorem fast_mean_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N : ℕ} (hN : 2 ≤ N)
    {B beta u : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hu : 0 < u) (hu1 : u < 1) :
    (∫ χJ : Randomness N B u × (Finset (Fin N) → ℝ),
      (normalized 2 N beta χJ.2 - fastRun N B beta u χJ.1 χJ.2)^2
        ∂(randomLaw N B u).prod (iidLaw μ)) ≤ u := by
  simp_rw [fastRun_eq_run hB hBT hu hu1]
  exact mean_square μ hμ hunit hN hB hBT hbeta hbetaB hu hu1

def fastCount (N : ℕ) (B beta epsilon delta : ℝ)
    (χ : Randomness N B (mseBudget 2 B epsilon delta)) (J : Finset (Fin N) → ℝ) : ℝ :=
  SpinGlass.logOutput (logBase 2 N beta J)
    (fastRun N B beta (mseBudget 2 B epsilon delta) χ J)

theorem fastCount_eq_count {N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1)
    (χ : Randomness N B (mseBudget 2 B epsilon delta)) (J : Finset (Fin N) → ℝ) :
    fastCount N B beta epsilon delta χ J = count N B beta epsilon delta χ J := by
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  unfold fastCount count
  rw [fastRun_eq_run hB hBT hu.1 hu.2]

/-- The full probability guarantee for the actual SK algorithm, uniformly in
every requested accuracy and temperature in the admissible interval. -/
theorem fast_counting_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N : ℕ} (hN : 2 ≤ N)
    {B beta epsilon delta : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    ((randomLaw N B (mseBudget 2 B epsilon delta)).prod (iidLaw μ)).real
      {χJ : Randomness N B (mseBudget 2 B epsilon delta) × (Finset (Fin N) → ℝ) |
        epsilon < |fastCount N B beta epsilon delta χJ.1 χJ.2 - targetLog 2 N beta χJ.2|} ≤
      remainder μ 2 N B + delta := by
  simp_rw [fastCount_eq_count hB hBT he he1 hd hd1]
  exact counting_probability μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1

end SpinGlass.SKUniformAlgorithm

namespace SpinGlass.SKCoefficientCorrectness
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual evaluator reads only genuine two-vertex input weights; its
intermediate tables may contain zero terms indexed by other pairs. -/
theorem estimator_congr (D L R : ℕ) (hL : 0 < L)
    (χ : Finset V → Fin R → V → Fin L) (f g : Finset V → ℝ)
    (hfg : ∀ e : Finset V, e.card = 2 → f e = g e) :
    SKActualEvaluator.estimator D L R χ f = SKActualEvaluator.estimator D L R χ g := by
  rw [estimator_eq_reference D L R hL, estimator_eq_reference D L R hL,
    SKReferenceAggregation.referenceEstimator_eq, SKReferenceAggregation.referenceEstimator_eq]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  have hprop := Finset.mem_filter.mp hΓ |>.1
  have he2 := Finset.mem_powerset.mp hprop he
  exact hfg e (Finset.mem_powersetCard.mp he2).2

/-- The cached physical input is exactly equivalent to direct physical weights
through every actual SK computation. -/
theorem estimator_prepared (D L R : ℕ) (hL : 0 < L)
    (χ : Finset V → Fin R → V → Fin L) (beta : ℝ) (J : Finset V → ℝ) :
    SKActualEvaluator.estimator D L R χ
      (InputPreparation.preparedWeight (InputPreparation.prepareInput 2 beta J)) =
      SKActualEvaluator.estimator D L R χ
        (fun e => Disorder.weight (Disorder.pureScale (Fintype.card V) 2 beta) (J e)) := by
  apply estimator_congr D L R hL
  intro e he
  exact InputPreparation.preparedWeight_value 2 beta J (by simp [he])

end SpinGlass.SKCoefficientCorrectness
