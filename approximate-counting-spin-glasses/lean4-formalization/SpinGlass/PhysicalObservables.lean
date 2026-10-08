import SpinGlass.PhysicalInput
import SpinGlass.SKTotalTheorem
import SpinGlass.HigherOrderTotalCost

/-! Physical-edge dependence and measurability of the final logarithmic outputs. -/
noncomputable section
namespace SpinGlass.PhysicalInput
open MeasureTheory
open scoped BigOperators
open SpinGlass.CountingReduction SpinGlass.Disorder SpinGlass.DesignConstants

/-- The target physical log partition reads only p-edges. -/
theorem targetLog_extend_restrict (p N : ℕ) (beta : ℝ) (J : Finset (Fin N) → ℝ) :
    targetLog p N beta (extend p (restrict p J)) = targetLog p N beta J := by
  unfold targetLog SpinGlass.Partition.partitionFunction
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  simp only [extend_restrict_edge p J he]

/-- This is the exact partition function on the actual edge subtype. -/
theorem targetLog_physical (p N : ℕ) (beta : ℝ) (J : Edge (Fin N) p → ℝ) :
    targetLog p N beta (extend p J) =
      Real.log (SpinGlass.Partition.partitionFunction (fun e : Edge (Fin N) p => e.val)
        Finset.univ (fun e => pureScale N p beta * J e)) := by
  unfold targetLog
  rw [Disorder.partitionFunction_restrict]
  congr 2
  funext e
  rw [extend_edge]

theorem measurable_targetLog (p N : ℕ) (beta : ℝ) : Measurable (targetLog p N beta) := by
  unfold targetLog SpinGlass.Partition.partitionFunction
  fun_prop

theorem measurable_logBase (p N : ℕ) (beta : ℝ) : Measurable (logBase p N beta) := by
  unfold logBase SpinGlass.Partition.prefactor
  fun_prop

theorem measurable_normalized (p N : ℕ) (beta : ℝ) : Measurable (normalized p N beta) := by
  unfold normalized SpinGlass.Partition.normalizedPartition SpinGlass.Partition.partitionFunction
    SpinGlass.Partition.prefactor
  fun_prop

/-- Input extension leaves the entire final SK computation, including its
counter, unchanged. Unused disorder coordinates are never queried. -/
theorem sk_countedTotal_extend_restrict {N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hd : 0 < delta)
    (χ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon delta))
    (J : Finset (Fin N) → ℝ) :
    SKTotalCost.countedTotal N B beta epsilon delta hB hBT hd χ (extend 2 (restrict 2 J)) =
      SKTotalCost.countedTotal N B beta epsilon delta hB hBT hd χ J := by
  simp only [SKTotalCost.countedTotal, prepareInput_extend_restrict]

/-- The analyzed SK output is a finite sum of measurable random coefficients
and continuous disorder monomials. -/
theorem measurable_sk_run (N : ℕ) (B beta u : ℝ) :
    Measurable (fun χJ : SKUniformAlgorithm.Randomness N B u × (Finset (Fin N) → ℝ) =>
      SKUniformAlgorithm.run N B beta u χJ.1 χJ.2) := by
  classical
  unfold SKUniformAlgorithm.run
  split_ifs
  · exact (measurable_normalized 2 N beta).comp measurable_snd
  · unfold SKRandomMeanSquare.estimator
    apply Finset.measurable_sum
    intro Γ hΓ
    exact ((measurable_of_finite (fun χ => SKRandomMeanSquare.coefficient
      (SKUniformAlgorithm.selectedSize N B u - 1) (SKUniformAlgorithm.edgeLimit B u)
      (SKUniformAlgorithm.repetitions B u) χ Γ)).comp measurable_fst).mul
        ((continuous_monomial (fun _ => pureScale N 2 beta) Γ).measurable.comp measurable_snd)

theorem measurable_sk_fastCount {N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    Measurable (fun χJ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon delta) ×
      (Finset (Fin N) → ℝ) => SKUniformAlgorithm.fastCount N B beta epsilon delta χJ.1 χJ.2) := by
  classical
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  simp only [SKUniformAlgorithm.fastCount, SpinGlass.logOutput]
  simp_rw [SKUniformAlgorithm.fastRun_eq_run hB hBT hu.1 hu.2]
  have hr := measurable_sk_run N B beta (mseBudget 2 B epsilon delta)
  exact ((measurable_logBase 2 N beta).comp measurable_snd).add
    (hr.log.ite (measurableSet_lt measurable_const hr) measurable_const)

/-- Measurability needed for exact physical-input probability transport. -/
theorem measurable_sk_error_event {N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    MeasurableSet {χJ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon delta) ×
      (Finset (Fin N) → ℝ) | epsilon <
      |(SKTotalCost.countedTotal N B beta epsilon delta hB hBT hd χJ.1 χJ.2).value -
        targetLog 2 N beta χJ.2|} := by
  simp_rw [SKTotalCost.countedTotal_value hB hBT he he1 hd hd1]
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((measurable_sk_fastCount (beta := beta) hB hBT he he1 hd hd1).sub
      ((measurable_targetLog 2 N beta).comp measurable_snd)))

/-- The deterministic higher-order execution also uses only the prepared input. -/
theorem higher_countedTotal_extend_restrict (p N : ℕ) (B beta epsilon delta : ℝ)
    (J : Finset (Fin N) → ℝ) :
    HigherOrderTotalCost.countedTotal p N B beta epsilon delta (extend p (restrict p J)) =
      HigherOrderTotalCost.countedTotal p N B beta epsilon delta J := by
  simp only [HigherOrderTotalCost.countedTotal, HigherOrderAlgorithm.countedCount,
    prepareInput_extend_restrict]

theorem measurable_higher_run (p N : ℕ) (B beta u : ℝ) :
    Measurable (fun J : Finset (Fin N) → ℝ => (HigherOrderAlgorithm.run p N B beta u J).value) := by
  classical
  unfold HigherOrderAlgorithm.run
  split_ifs
  · simp only [SupportEvaluation.exactEvaluator_disorder_value]
    exact measurable_normalized p N beta
  · simp only [SupportEvaluation.higherEvaluator_disorder_value, SupportMeanSquare.supportApproximation]
    exact Finset.measurable_sum _ (fun Γ _ => (continuous_monomial _ Γ).measurable)

theorem measurable_higher_count (p N : ℕ) (B beta epsilon delta : ℝ) :
    Measurable (HigherOrderAlgorithm.count p N B beta epsilon delta) := by
  classical
  unfold HigherOrderAlgorithm.count SpinGlass.logOutput
  have hr := measurable_higher_run p N B beta (mseBudget p B epsilon delta)
  exact (measurable_logBase p N beta).add
    (hr.log.ite (measurableSet_lt measurable_const hr) measurable_const)

theorem measurable_higher_error_event {p N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hd : 0 < delta) :
    MeasurableSet {J : Finset (Fin N) → ℝ | epsilon <
      |(HigherOrderTotalCost.countedTotal p N B beta epsilon delta J).value -
        targetLog p N beta J|} := by
  simp_rw [HigherOrderTotalCost.countedTotal_value, HigherOrderAlgorithm.countedCount_value hB hBT hd]
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((measurable_higher_count p N B beta epsilon delta).sub
      (measurable_targetLog p N beta)))

end SpinGlass.PhysicalInput
