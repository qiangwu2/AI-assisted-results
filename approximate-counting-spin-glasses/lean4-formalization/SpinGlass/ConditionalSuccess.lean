import SpinGlass.SKTotalTheorem
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Conditional success from joint success

A joint color/disorder failure bound gives a fixed-instance color failure bound
outside a disorder set of square-root probability, including the zero-error case.
-/
noncomputable section
namespace SpinGlass.ConditionalSuccess
open MeasureTheory
open scoped ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Failure probability over colors for one fixed disorder instance. -/
def conditionalFailure (P : Measure Ω) (E : Set (Ω × X)) (x : X) : ℝ :=
  P.real {ω | (ω,x) ∈ E}

/-- The section-9.1 Markov step on the actual product probability space. -/
theorem conditional_markov (P : Measure Ω) (Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set (Ω × X)) (hE : MeasurableSet E) {zeta : ℝ}
    (hz : 0 ≤ zeta) (hjoint : (P.prod Q).real E ≤ zeta) :
    Q.real {x | Real.sqrt zeta < conditionalFailure P E x} ≤ Real.sqrt zeta := by
  let q : X → ℝ≥0∞ := fun x => P {ω | (ω,x) ∈ E}
  have hq : Measurable q := measurable_measure_prodMk_right hE
  have hprod : ∫⁻ x, q x ∂Q = (P.prod Q) E := (Measure.prod_apply_symm hE).symm
  by_cases hzero : zeta = 0
  · subst zeta
    have hp0 : (P.prod Q).real E = 0 := le_antisymm hjoint measureReal_nonneg
    have hp : (P.prod Q) E = 0 := (measureReal_eq_zero_iff).mp hp0
    have hae : q =ᵐ[Q] 0 := (lintegral_eq_zero_iff hq).mp (hprod.trans hp)
    have hbad : Q {x | Real.sqrt 0 < conditionalFailure P E x} = 0 := by
      apply measure_mono_null (t := {x | q x ≠ 0})
      · intro x hx
        change q x ≠ 0
        intro hx0
        have hh : conditionalFailure P E x = 0 := by
          change (q x).toReal = 0
          rw [hx0, ENNReal.toReal_zero]
        simpa [hh] using hx
      · exact ae_iff.mp hae
    rw [(measureReal_eq_zero_iff).mpr hbad, Real.sqrt_zero]
  · have hzpos : 0 < zeta := lt_of_le_of_ne hz (Ne.symm hzero)
    have hspos := Real.sqrt_pos.mpr hzpos
    have hsnonneg := Real.sqrt_nonneg zeta
    have hmark := mul_meas_ge_le_lintegral (μ := Q) hq (ENNReal.ofReal (Real.sqrt zeta))
    rw [hprod] at hmark
    have hmreal : Real.sqrt zeta * Q.real {x | ENNReal.ofReal (Real.sqrt zeta) ≤ q x} ≤
        (P.prod Q).real E := by
      have ht := ENNReal.toReal_mono (measure_ne_top (P.prod Q) E) hmark
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hsnonneg, Measure.real] using ht
    have hsub : {x | Real.sqrt zeta < conditionalFailure P E x} ⊆
        {x | ENNReal.ofReal (Real.sqrt zeta) ≤ q x} := by
      intro x hx
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P _)).mpr hx.le
    have hle := measureReal_mono (μ := Q) hsub
    have hsquare := Real.sq_sqrt hz
    nlinarith

open SpinGlass.CountingReduction SpinGlass.DesignConstants SpinGlass.Disorder

/-- Every fixed-color graph estimator is a finite continuous polynomial in the
physical bounded weights. -/
theorem measurable_run (N : ℕ) (B beta u : ℝ) (χ : SKUniformAlgorithm.Randomness N B u) :
    Measurable (SKUniformAlgorithm.run N B beta u χ) := by
  classical
  unfold SKUniformAlgorithm.run
  split_ifs
  · unfold SpinGlass.Partition.normalizedPartition SpinGlass.Partition.partitionFunction
      SpinGlass.Partition.prefactor
    fun_prop
  · unfold SpinGlass.SKRandomMeanSquare.estimator
    apply Finset.measurable_sum
    intro Γ hΓ
    exact measurable_const.mul (continuous_monomial _ Γ).measurable

theorem measurable_logBase (p N : ℕ) (beta : ℝ) : Measurable (logBase p N beta) := by
  unfold logBase SpinGlass.Partition.prefactor
  fun_prop

theorem measurable_targetLog (p N : ℕ) (beta : ℝ) : Measurable (targetLog p N beta) := by
  unfold targetLog SpinGlass.Partition.partitionFunction
  fun_prop

theorem measurable_count (N : ℕ) (B beta epsilon delta : ℝ)
    (χ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon delta)) :
    Measurable (SKUniformAlgorithm.count N B beta epsilon delta χ) := by
  classical
  have hr := measurable_run N B beta (mseBudget 2 B epsilon delta) χ
  have hb := measurable_logBase 2 N beta
  unfold SKUniformAlgorithm.count SpinGlass.logOutput
  exact hb.add (Measurable.ite (measurableSet_lt measurable_const hr)
    (Real.measurable_log.comp hr) measurable_const)

/-- The actual final total-cost output has a measurable joint failure event. -/
theorem measurable_sk_failure {N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    MeasurableSet {χJ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon delta) ×
        (Finset (Fin N) → ℝ) |
      epsilon < |(SKTotalCost.countedTotal N B beta epsilon delta hB hBT hd χJ.1 χJ.2).value -
        targetLog 2 N beta χJ.2|} := by
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  simp_rw [SKTotalCost.countedTotal_value hB hBT he he1 hd hd1,
    SKUniformAlgorithm.fastCount_eq_count hB hBT he he1 hd hd1]
  have hc : Measurable (fun χJ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon delta) ×
        (Finset (Fin N) → ℝ) => SKUniformAlgorithm.count N B beta epsilon delta χJ.1 χJ.2) :=
    measurable_from_prod_countable_right (fun χ => measurable_count N B beta epsilon delta χ)
  have ht : Measurable (fun χJ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon delta) ×
        (Finset (Fin N) → ℝ) => targetLog 2 N beta χJ.2) :=
    (measurable_targetLog 2 N beta).comp measurable_snd
  apply measurableSet_lt measurable_const
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hc.sub ht).norm

/-- Section9.1 for the actual final algorithm: all but sqrt(zeta) of disorder
instances have color-conditional failure probability at most sqrt(zeta). -/
theorem sk_conditional_success (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N : ℕ} (hN : 2 ≤ N) {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1)
    {zeta : ℝ} (hz : 0 ≤ zeta) (htail : remainder μ 2 N B + delta ≤ zeta) :
    (iidLaw μ).real {J : Finset (Fin N) → ℝ |
      Real.sqrt zeta < (SKUniformAlgorithm.randomLaw N B (mseBudget 2 B epsilon delta)).real
        {χ | epsilon < |(SKTotalCost.countedTotal N B beta epsilon delta hB hBT hd χ J).value -
          targetLog 2 N beta J|}} ≤ Real.sqrt zeta := by
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  letI := SKUniformAlgorithm.randomLaw_probability (N := N) hB hBT hu.1 hu.2
  exact conditional_markov _ _ _ (measurable_sk_failure hB hBT he he1 hd hd1) hz
    ((SKTotalCost.counted_probability μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1).trans htail)

/-- The completely discharged fixed-instance bound with zeta=delta+tau. -/
theorem sk_conditional_remainder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N : ℕ} (hN : 2 ≤ N) {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    (iidLaw μ).real {J : Finset (Fin N) → ℝ |
      Real.sqrt (remainder μ 2 N B + delta) <
        (SKUniformAlgorithm.randomLaw N B (mseBudget 2 B epsilon delta)).real
          {χ | epsilon < |(SKTotalCost.countedTotal N B beta epsilon delta hB hBT hd χ J).value -
            targetLog 2 N beta J|}} ≤ Real.sqrt (remainder μ 2 N B + delta) := by
  apply sk_conditional_success μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1
  · have hr : 0 ≤ remainder μ 2 N B := by
      unfold remainder disorderTailRemainder
      exact mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
    linarith
  · exact le_rfl

end SpinGlass.ConditionalSuccess
