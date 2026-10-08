import SpinGlass.SKAlgorithm
import SpinGlass.SKRuntime
import SpinGlass.SKCountedExecution

/-! # Counted SK execution with physical-input preparation and automatic cutoffs -/
noncomputable section
namespace SpinGlass.SKUniformAlgorithm
open Finset Real MeasureTheory
open SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation SpinGlass.SupportEvaluation
open SpinGlass.DesignConstants SpinGlass.CountingReduction SpinGlass.AlgorithmBudgets
open SpinGlass.BoundedSearch SpinGlass.PolynomialRuntime

def cachedEvaluator (N : ℕ) (B u : ℝ) (χ : Randomness N B u)
    (input : PreparedInput (Fin N)) : Computation := by
  classical
  exact if exactBranch N B u then exactEvaluator 2 (preparedWeight input)
  else
    let r := SpinGlass.SKCountedExecution.estimator (selectedSize N B u - 1)
        (edgeLimit B u) (repetitions B u) χ (preparedWeight input)
    ⟨r.value,r.operations⟩

def scanEvaluations (N : ℕ) (B u : ℝ) : ℕ := by
  classical
  exact if exactBranch N B u then 0 else
    (cutoffScan 1 (branchScale B) (alpha B) N (budget B u)).evaluations

def execute (N : ℕ) (B beta u : ℝ) (χ : Randomness N B u)
    (J : Finset (Fin N) → ℝ) : Computation :=
  let input := prepareInput 2 beta J
  let lambda := logarithm (divide (literal (budgetConstant B)) (literal u))
  let result := cachedEvaluator N B u χ input
  ⟨result.value,input.operations + lambda.operations + 3 + 6 * scanEvaluations N B u + result.operations⟩

theorem cachedEvaluator_value {N : ℕ} {B beta u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    (cachedEvaluator N B u χ (prepareInput 2 beta J)).value = fastRun N B beta u χ J := by
  classical
  by_cases he : exactBranch N B u
  · simp only [cachedEvaluator, fastRun, if_pos he, prepared_exactEvaluator_value,
      exactEvaluator_disorder_value, Fintype.card_fin]
  · simp only [cachedEvaluator, fastRun, if_neg he, SKCountedExecution.estimator_value]
    simpa only [Fintype.card_fin] using SKCoefficientCorrectness.estimator_prepared
      (selectedSize N B u - 1) (edgeLimit B u) (repetitions B u) (edgeLimit_pos hB hBT hu hu1) χ beta J

theorem execute_value {N : ℕ} {B beta u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    (execute N B beta u χ J).value = fastRun N B beta u χ J :=
  cachedEvaluator_value hB hBT hu hu1 χ J

theorem execute_operations (N : ℕ) (B beta u : ℝ)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    (execute N B beta u χ J).operations = (prepareInput 2 beta J).operations + 5 +
      6 * scanEvaluations N B u + (cachedEvaluator N B u χ (prepareInput 2 beta J)).operations := by
  simp only [execute,logarithm,divide,literal]

theorem scanEvaluations_le {N : ℕ} {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) : scanEvaluations N B u ≤ N := by
  classical
  have h := valid hB hBT
  unfold scanEvaluations
  split_ifs
  · omega
  · exact cutoffScan_evaluations h.alpha_pos.le h.alpha_le

theorem cachedEvaluator_envelope {N : ℕ} (hN : 2 ≤ N) {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (χ : Randomness N B u) (input : PreparedInput (Fin N)) :
    ((cachedEvaluator N B u χ input).operations : ℝ) ≤
      amplitude B * ((N : ℝ)+1)^5 * Real.exp (growth B * budget B u) := by
  classical
  by_cases he : exactBranch N B u
  · have hcount := exactEvaluator_cost (V := Fin N) (p := 2) (by omega) (preparedWeight input)
    have hcountR : ((cachedEvaluator N B u χ input).operations : ℝ) ≤
        8 * ((N : ℝ)+1)^2 * (2 : ℝ)^N := by
      simp only [cachedEvaluator,if_pos he]
      exact_mod_cast (by simpa only [Fintype.card_fin] using hcount)
    exact hcountR.trans (exact_envelope hN hB hBT hu hu1 he)
  · have hs := selectedSize_spec hB hBT hu hu1 he
    have hm : selectedSize N B u - 1 + 1 = selectedSize N B u := by omega
    have hcount := SKCountedExecution.estimator_operations_le
      (selectedSize N B u - 1) (edgeLimit B u) (repetitions B u)
      (repetitions_pos B u) χ (preparedWeight input)
    have hcountR : ((cachedEvaluator N B u χ input).operations : ℝ) ≤ 64 * approximateWork N B u := by
      simp only [cachedEvaluator,if_neg he]
      dsimp [approximateWork]
      exact_mod_cast (by simpa only [Fintype.card_fin,hm,Nat.mul_assoc] using hcount)
    have happrox := approximate_envelope hN hB hBT hu hu1 he
    have hA : 64 * colorAmplitude B ≤ amplitude B := amplitude_ge_color
    calc
      _ ≤ 64 * (colorAmplitude B * ((N : ℝ)+1)^5 * Real.exp (growth B * budget B u)) :=
        hcountR.trans (mul_le_mul_of_nonneg_left happrox (by norm_num))
      _ = (64 * colorAmplitude B) * ((N : ℝ)+1)^5 * Real.exp (growth B * budget B u) := by ring
      _ ≤ _ := by gcongr

def executionAmplitude (B : ℝ) : ℝ := amplitude B + 27

theorem execution_envelope {N : ℕ} (hN : 2 ≤ N) {B beta u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    ((execute N B beta u χ J).operations : ℝ) ≤
      executionAmplitude B * ((N : ℝ)+1)^5 * Real.exp (growth B * budget B u) := by
  have h := valid hB hBT
  have hLam := logBudget_pos h.budget_ge hu hu1
  have hexp : 1 ≤ Real.exp (growth B * budget B u) :=
    Real.one_le_exp_iff.mpr (mul_pos (growth_pos hB hBT) hLam).le
  have hNp : (1 : ℝ) ≤ (N : ℝ)+1 := by have := (Nat.cast_nonneg N : (0:ℝ) ≤ N); linarith
  have hP : 1 ≤ ((N : ℝ)+1)^5 := one_le_pow₀ hNp
  have hNpow : (N : ℝ) ≤ ((N : ℝ)+1)^5 :=
    (by linarith : (N : ℝ) ≤ (N : ℝ)+1).trans (le_self_pow₀ hNp (by omega))
  have hpow : ((N : ℝ)+1)^2 ≤ ((N : ℝ)+1)^5 := pow_le_pow_right₀ hNp (by omega)
  have hprep : ((prepareInput 2 beta J).operations : ℝ) ≤ 16*((N : ℝ)+1)^2 := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using prepareInput_cost (V := Fin N) (by omega : 0<2) beta J)
  have hscan : (scanEvaluations N B u : ℝ) ≤ N := by exact_mod_cast scanEvaluations_le (N := N) (u := u) hB hBT
  have hbase := cachedEvaluator_envelope hN hB hBT hu hu1 χ (prepareInput 2 beta J)
  have hsetup : ((prepareInput 2 beta J).operations : ℝ) + 5 + 6*scanEvaluations N B u ≤
      27*((N : ℝ)+1)^5 := by nlinarith
  rw [execute_operations]
  push_cast
  unfold executionAmplitude
  nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 27*((N : ℝ)+1)^5)]

theorem execution_polynomial {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ beta u : ℝ, 0 < u → u < 1 →
      ∀ (χ : Randomness N B u) (J : Finset (Fin N) → ℝ),
        ((execute N B beta u χ J).operations : ℝ) ≤ C*(N : ℝ)^C*u^(-C) := by
  let C := envelopeConstant (executionAmplitude B) (budgetConstant B) (growth B) 5
  refine ⟨C,envelopeConstant_pos _ _ _ _,?_⟩
  intro N hN beta u hu hu1 χ J
  have h := valid hB hBT
  have hA := amplitude_ge_exact hB hBT
  have hA0 : 0 ≤ executionAmplitude B := by
    have h2 : 0 < (2 : ℝ)^(sizeLimit B) := by positivity
    unfold executionAmplitude
    linarith
  exact (execution_envelope hN hB hBT hu hu1 χ J).trans
    (envelope_le_polynomial hA0 (by linarith [h.budget_ge]) (by omega) hu hu1.le)

end SpinGlass.SKUniformAlgorithm
