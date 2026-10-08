import SpinGlass.SKTotalExecution
import SpinGlass.AccuracyRuntime

/-! # End-to-end accuracy and total operation cost of the actual randomized SK execution -/
noncomputable section
namespace SpinGlass.SKTotalCost
open Finset Real MeasureTheory
open SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation SpinGlass.SupportEvaluation
open SpinGlass.DesignConstants SpinGlass.CountingReduction SpinGlass.AccuracyRuntime
open SpinGlass.SKUniformAlgorithm

theorem cachedTotal_transport {N : ℕ} {B u v : ℝ} (h : u = v)
    (χ : Randomness N B v) (input : PreparedInput (Fin N)) :
    cachedTotal N B u (h.symm ▸ χ) input = cachedTotal N B v χ input := by
  cases h
  rfl

/-- Full counted execution. The proof arguments certify the fixed admissible
temperature margin and positive requested confidence; they perform no computation.
The actual computed budget is used, with the color-array index transported along
the proved budget identity. -/
def countedTotal (N : ℕ) (B beta epsilon delta : ℝ)
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hd : 0 < delta)
    (χ : Randomness N B (mseBudget 2 B epsilon delta)) (J : Finset (Fin N) → ℝ) : Computation := by
  classical
  let b := prepareBudget (constant 2 B) delta epsilon (exponent 2 B)
  have hC : 0 < constant 2 B := zero_lt_one.trans_le (constant_ge_one hB hBT)
  have hu : b.u = mseBudget 2 B epsilon delta := prepareBudget_u hC hd
  let colors : Randomness N B b.u := hu.symm ▸ χ
  let input := prepareInput 2 beta J
  let lambda := logarithm (divide (literal (budgetConstant B)) (literal b.u))
  let correction := cachedTotal N B b.u colors input
  let logCorrection := if 0 < correction.value then logarithm (literal correction.value) else literal 0
  let result := add (literal input.logPrefactor) logCorrection
  exact ⟨result.value,b.operations + input.operations + lambda.operations + 3 +
    6 * scanEvaluations N B b.u + HigherOrderControl.setupControl 2 N + correction.operations + 1 + result.operations⟩

theorem countedTotal_value {N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1)
    (χ : Randomness N B (mseBudget 2 B epsilon delta)) (J : Finset (Fin N) → ℝ) :
    (countedTotal N B beta epsilon delta hB hBT hd χ J).value =
      fastCount N B beta epsilon delta χ J := by
  classical
  have hC : 0 < constant 2 B := zero_lt_one.trans_le (constant_ge_one hB hBT)
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  have hbudget : (prepareBudget (constant 2 B) delta epsilon (exponent 2 B)).u =
      mseBudget 2 B epsilon delta := prepareBudget_u hC hd
  have hcache := cachedTotal_transport hbudget χ (prepareInput 2 beta J)
  simp only [countedTotal]
  rw [hcache]
  rw [cachedTotal_value, cachedEvaluator_value hB hBT hu.1 hu.2 χ J]
  simp only [mseBudget] at χ ⊢
  simp only [add,literal,logarithm,
    fastCount,SpinGlass.logOutput,prepareInput_logPrefactor,Fintype.card_fin,logBase,mseBudget]
  split_ifs <;> rfl

theorem countedTotal_operations {N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hd : 0 < delta)
    (χ : Randomness N B (mseBudget 2 B epsilon delta)) (J : Finset (Fin N) → ℝ) :
    (countedTotal N B beta epsilon delta hB hBT hd χ J).operations ≤
      (execute N B beta (mseBudget 2 B epsilon delta) χ J).operations + 13 := by
  classical
  have hC : 0 < constant 2 B := zero_lt_one.trans_le (constant_ge_one hB hBT)
  have hbudget : (prepareBudget (constant 2 B) delta epsilon (exponent 2 B)).u =
      mseBudget 2 B epsilon delta := prepareBudget_u hC hd
  have hcache := cachedTotal_transport hbudget χ (prepareInput 2 beta J)
  simp only [countedTotal]
  rw [hcache]
  simp only [prepareBudget_u hC hd,prepareBudget_operations,execute_operations]
  simp only [mseBudget] at χ ⊢
  simp only [logarithm,divide,literal,add]
  split_ifs <;> simp only [logarithm,literal] <;> omega

theorem counted_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SpinGlass.Disorder.SymmetricLaw μ) (hunit : SpinGlass.Disorder.UnitSecondMoment μ)
    {N : ℕ} (hN : 2 ≤ N) {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    ((randomLaw N B (mseBudget 2 B epsilon delta)).prod (SpinGlass.Disorder.iidLaw μ)).real
      {χJ : Randomness N B (mseBudget 2 B epsilon delta) × (Finset (Fin N) → ℝ) |
        epsilon < |(countedTotal N B beta epsilon delta hB hBT hd χJ.1 χJ.2).value -
          targetLog 2 N beta χJ.2|} ≤ remainder μ 2 N B + delta := by
  simp_rw [countedTotal_value hB hBT he he1 hd hd1]
  exact fast_counting_probability μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1

theorem counted_polynomial {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ (beta epsilon delta : ℝ),
      0 < epsilon → epsilon < 1 → ∀ hd : 0 < delta, delta < 1 →
      ∀ (χ : Randomness N B (mseBudget 2 B epsilon delta)) (J : Finset (Fin N) → ℝ),
      ((countedTotal N B beta epsilon delta hB hBT hd χ J).operations : ℝ) ≤
        C*(N:ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨k,hk,hwork⟩ := execution_polynomial hB hBT
  let D := countingConstant (k+13) (constant 2 B) (exponent 2 B) k
  refine ⟨D,countingConstant_pos _ _ _ _,?_⟩
  intro N hN beta epsilon delta he he1 hd hd1 χ J
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  have hC : 0 < constant 2 B := zero_lt_one.trans_le (constant_ge_one hB hBT)
  have hcount : ((countedTotal N B beta epsilon delta hB hBT hd χ J).operations : ℝ) ≤
      ((execute N B beta (mseBudget 2 B epsilon delta) χ J).operations : ℝ) + 13 := by
    exact_mod_cast countedTotal_operations hB hBT hd χ J
  have hmain := hwork N hN beta (mseBudget 2 B epsilon delta) hu.1 hu.2 χ J
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNP : 1 ≤ (N:ℝ)^k := Real.one_le_rpow hNR hk.le
  have huP : 1 ≤ (mseBudget 2 B epsilon delta)^(-k) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu.1 hu.2.le (by linarith)
  have hP : 1 ≤ (N:ℝ)^k*(mseBudget 2 B epsilon delta)^(-k) := by nlinarith
  have hbound : ((countedTotal N B beta epsilon delta hB hBT hd χ J).operations : ℝ) ≤
      (k+13)*(N:ℝ)^k*(mseBudget 2 B epsilon delta)^(-k) := by nlinarith
  exact hbound.trans (budget_polynomial (by linarith : 0 ≤ k+13) hC (by omega) hd hd1.le he he1.le)

theorem end_to_end {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      SpinGlass.Disorder.SymmetricLaw μ → SpinGlass.Disorder.UnitSecondMoment μ →
      ∀ (N : ℕ), 2 ≤ N → ∀ (beta epsilon delta : ℝ), 0 ≤ beta → beta ≤ B →
        0 < epsilon → epsilon < 1 → ∀ hd : 0 < delta, delta < 1 →
      (((randomLaw N B (mseBudget 2 B epsilon delta)).prod (SpinGlass.Disorder.iidLaw μ)).real
        {χJ : Randomness N B (mseBudget 2 B epsilon delta) × (Finset (Fin N) → ℝ) |
          epsilon < |(countedTotal N B beta epsilon delta hB hBT hd χJ.1 χJ.2).value -
            targetLog 2 N beta χJ.2|} ≤ remainder μ 2 N B + delta) ∧
      (∀ (χ : Randomness N B (mseBudget 2 B epsilon delta)) (J : Finset (Fin N) → ℝ),
        ((countedTotal N B beta epsilon delta hB hBT hd χ J).operations : ℝ) ≤
          C*(N:ℝ)^C*epsilon^(-C)*delta^(-C)) := by
  obtain ⟨C,hC,hcost⟩ := counted_polynomial hB hBT
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N hN beta epsilon delta hbeta hbetaB he he1 hd hd1
  exact ⟨counted_probability μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1,
    hcost N hN beta epsilon delta he he1 hd hd1⟩

end SpinGlass.SKTotalCost
