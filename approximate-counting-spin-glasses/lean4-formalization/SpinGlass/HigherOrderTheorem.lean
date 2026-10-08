import SpinGlass.HigherOrderExecution
import SpinGlass.AccuracyRuntime

/-! End-to-end arithmetic-oracle counting for pure p-spin with p at least three. -/

noncomputable section
namespace SpinGlass.HigherOrderAlgorithm
open Finset Real MeasureTheory
open SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation SpinGlass.SupportEvaluation
open SpinGlass.DesignConstants SpinGlass.CountingReduction SpinGlass.AccuracyRuntime

/-- The complete execution computes its own weights, log prefactor, accuracy
budget, bounded cutoff scan, correction, and final logarithmic output. -/
def countedCount (p N : ℕ) (B beta epsilon delta : ℝ) (J : Finset (Fin N) → ℝ) : Computation := by
  classical
  let b := prepareBudget (constant p B) delta epsilon (exponent p B)
  let input := prepareInput p beta J
  let lambda := logarithm (divide (literal (budgetConstant p B)) (literal b.u))
  let correction := cachedEvaluator p N B b.u input
  let logCorrection := if 0 < correction.value then logarithm (literal correction.value) else literal 0
  let result := add (literal input.logPrefactor) logCorrection
  exact ⟨result.value, b.operations + input.operations + lambda.operations + 3 +
    6 * scanEvaluations p N B b.u + correction.operations + 1 + result.operations⟩

theorem countedCount_value {p N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hd : 0 < delta) (J : Finset (Fin N) → ℝ) :
    (countedCount p N B beta epsilon delta J).value = count p N B beta epsilon delta J := by
  classical
  have hC : 0 < constant p B := lt_of_lt_of_le zero_lt_one (constant_ge_one hB hBT)
  simp only [countedCount, prepareBudget_u hC hd, add, literal, logarithm,
    cachedEvaluator_value, count, SpinGlass.logOutput]
  rw [prepareInput_logPrefactor]
  simp only [Fintype.card_fin, logBase, mseBudget]
  split_ifs <;> rfl

theorem countedCount_operations {p N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hd : 0 < delta) (J : Finset (Fin N) → ℝ) :
    (countedCount p N B beta epsilon delta J).operations ≤
      (execute p N B beta (mseBudget p B epsilon delta) J).operations + 13 := by
  classical
  have hC : 0 < constant p B := lt_of_lt_of_le zero_lt_one (constant_ge_one hB hBT)
  rw [execute_operations]
  simp only [countedCount, prepareBudget_operations, prepareBudget_u hC hd,
    logarithm, divide, literal, cachedEvaluator_operations, add, mseBudget]
  split_ifs <;> simp only [logarithm, literal] <;> omega

/-- The final probability theorem for the completely counted execution. -/
theorem counted_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SpinGlass.Disorder.SymmetricLaw μ) (hunit : SpinGlass.Disorder.UnitSecondMoment μ)
    {p N : ℕ} (hp : 3 ≤ p) (hpN : p ≤ N) {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    (SpinGlass.Disorder.iidLaw μ).real {J : Finset (Fin N) → ℝ |
      epsilon < |(countedCount p N B beta epsilon delta J).value - targetLog p N beta J|} ≤
      remainder μ p N B + delta := by
  simp_rw [countedCount_value hB hBT hd]
  exact counting_probability μ hμ hunit hp hpN hB hBT hbeta hbetaB he he1 hd hd1

/-- A single fixed exponent bounds the whole execution in N, inverse
accuracy, and inverse confidence, including all input and output arithmetic. -/
theorem counted_polynomial {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), p ≤ N → ∀ (beta epsilon delta : ℝ),
      0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ∀ J : Finset (Fin N) → ℝ,
      ((countedCount p N B beta epsilon delta J).operations : ℝ) ≤
        C*(N:ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨k, hk, hwork⟩ := execution_polynomial hp hB hBT
  let D := countingConstant (k+13) (constant p B) (exponent p B) k
  refine ⟨D, countingConstant_pos _ _ _ _, ?_⟩
  intro N hpN beta epsilon delta he he1 hd hd1 J
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  have hC : 0 < constant p B := lt_of_lt_of_le zero_lt_one (constant_ge_one hB hBT)
  have hcount : ((countedCount p N B beta epsilon delta J).operations : ℝ) ≤
      ((execute p N B beta (mseBudget p B epsilon delta) J).operations : ℝ) + 13 := by
    exact_mod_cast countedCount_operations hB hBT hd J
  have hmain := hwork N hpN beta (mseBudget p B epsilon delta) hu.1 hu.2 J
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNP : 1 ≤ (N:ℝ)^k := Real.one_le_rpow hN hk.le
  have huP : 1 ≤ (mseBudget p B epsilon delta)^(-k) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu.1 hu.2.le (by linarith)
  have hP : 1 ≤ (N:ℝ)^k*(mseBudget p B epsilon delta)^(-k) := by nlinarith
  have hbound : ((countedCount p N B beta epsilon delta J).operations : ℝ) ≤
      (k+13)*(N:ℝ)^k*(mseBudget p B epsilon delta)^(-k) := by
    nlinarith
  exact hbound.trans (budget_polynomial (by linarith : 0 ≤ k+13) hC (by omega) hd hd1.le he he1.le)

/-- Joint correctness and arithmetic complexity for the actual deterministic
algorithm, under exactly the pure-spin hypotheses with p at least three. -/
theorem end_to_end {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      SpinGlass.Disorder.SymmetricLaw μ → SpinGlass.Disorder.UnitSecondMoment μ →
      ∀ (N : ℕ), p ≤ N → ∀ (beta epsilon delta : ℝ), 0 ≤ beta → beta ≤ B →
        0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ((SpinGlass.Disorder.iidLaw μ).real {J : Finset (Fin N) → ℝ |
        epsilon < |(countedCount p N B beta epsilon delta J).value - targetLog p N beta J|} ≤
          remainder μ p N B + delta) ∧
      (∀ J : Finset (Fin N) → ℝ, ((countedCount p N B beta epsilon delta J).operations : ℝ) ≤
        C*(N:ℝ)^C*epsilon^(-C)*delta^(-C)) := by
  obtain ⟨C, hC, hcost⟩ := counted_polynomial hp hB hBT
  refine ⟨C, hC, ?_⟩
  intro μ hprob hμ hunit N hpN beta epsilon delta hbeta hbetaB he he1 hd hd1
  exact ⟨counted_probability μ hμ hunit hp hpN hB hBT hbeta hbetaB he he1 hd hd1,
    hcost N hpN beta epsilon delta he he1 hd hd1⟩

end SpinGlass.HigherOrderAlgorithm
