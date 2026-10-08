import SpinGlass.HigherOrderCounting
import SpinGlass.InputPreparation

/-! Cached input preparation and the bounded scan are included in the counted
higher-order execution. Real arithmetic and elementary oracles are counted. -/

noncomputable section
namespace SpinGlass.HigherOrderAlgorithm
open Finset Real MeasureTheory
open SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation SpinGlass.SupportEvaluation
open SpinGlass.DesignConstants SpinGlass.CountingReduction SpinGlass.AlgorithmBudgets
open SpinGlass.BoundedSearch SpinGlass.PolynomialRuntime SpinGlass.SupportMassBound

def cachedEvaluator (p N : ℕ) (B u : ℝ) (input : PreparedInput (Fin N)) : Computation := by
  classical
  exact if exactBranch p N B u then exactEvaluator p (preparedWeight input)
    else higherEvaluator p (selectedSize p N B u - 1) (preparedWeight input)

def scanEvaluations (p N : ℕ) (B u : ℝ) : ℕ := by
  classical
  exact if exactBranch p N B u then 0 else
    (cutoffScan (kappa p) (supportScale p B) (alpha p B) N (budget p B u)).evaluations

/-- One cutoff test evaluates Phi in five elementary operations and compares
it with the budget once. -/
def phiComputation (kap a N t : ℝ) : Computation :=
  mul (mul (literal kap) (literal t))
    (logarithm (divide (literal N) (mul (literal a) (literal t))))

@[simp] theorem phiComputation_value (kap a N t : ℝ) :
    (phiComputation kap a N t).value = SpinGlass.CutoffTail.phi kap a N t := rfl
@[simp] theorem phiComputation_operations (kap a N t : ℝ) :
    (phiComputation kap a N t).operations = 5 := rfl

/-- Input preparation includes the physical weights and log prefactor.
The two budget operations, branch tests, and actual bounded scan are charged
in addition to the selected evaluator. -/
def execute (p N : ℕ) (B beta u : ℝ) (J : Finset (Fin N) → ℝ) : Computation :=
  let input := prepareInput p beta J
  let lambda := logarithm (divide (literal (budgetConstant p B)) (literal u))
  let result := cachedEvaluator p N B u input
  ⟨result.value, input.operations + lambda.operations + 3 +
    6 * scanEvaluations p N B u + result.operations⟩

theorem cachedEvaluator_value (p N : ℕ) (B beta u : ℝ) (J : Finset (Fin N) → ℝ) :
    (cachedEvaluator p N B u (prepareInput p beta J)).value = (run p N B beta u J).value := by
  classical
  by_cases he : exactBranch p N B u
  · simp only [cachedEvaluator, run, if_pos he, prepared_exactEvaluator_value,
      exactEvaluator_disorder_value, Fintype.card_fin]
  · simp only [cachedEvaluator, run, if_neg he, prepared_higherEvaluator_value,
      higherEvaluator_disorder_value, Fintype.card_fin]

theorem cachedEvaluator_operations (p N : ℕ) (B beta u : ℝ) (J : Finset (Fin N) → ℝ) :
    (cachedEvaluator p N B u (prepareInput p beta J)).operations = (run p N B beta u J).operations := by
  classical
  by_cases he : exactBranch p N B u
  · simp only [cachedEvaluator, run, if_pos he, exactEvaluator, localEvaluator_operations]
  · simp only [cachedEvaluator, run, if_neg he, higherEvaluator, sumFinset_operations,
      supportEvaluator_operations, localEvaluator_operations]

@[simp] theorem execute_value (p N : ℕ) (B beta u : ℝ) (J : Finset (Fin N) → ℝ) :
    (execute p N B beta u J).value = (run p N B beta u J).value := cachedEvaluator_value _ _ _ _ _ _

theorem execute_operations (p N : ℕ) (B beta u : ℝ) (J : Finset (Fin N) → ℝ) :
    (execute p N B beta u J).operations = (prepareInput p beta J).operations + 5 +
      6 * scanEvaluations p N B u + (run p N B beta u J).operations := by
  simp only [execute, logarithm, divide, literal, cachedEvaluator_operations]

theorem scanEvaluations_le {p N : ℕ} {B u : ℝ} (hp : 3 ≤ p) (hB : 0 < B)
    (hBT : B < betaThreshold p) : scanEvaluations p N B u ≤ N := by
  classical
  have h := valid hp hB hBT
  unfold scanEvaluations
  split_ifs
  · omega
  · exact cutoffScan_evaluations h.alpha_pos.le h.alpha_le

def executionAmplitude (p : ℕ) (B : ℝ) : ℝ := amplitude p B + p + 25

theorem execution_envelope {p N : ℕ} (hp : 3 ≤ p) (hpN : p ≤ N) {B beta u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hu : 0 < u) (hu1 : u < 1)
    (J : Finset (Fin N) → ℝ) :
    ((execute p N B beta u J).operations : ℝ) ≤
      executionAmplitude p B * ((N:ℝ)+1)^(p+1) * Real.exp (growth p B * budget p B u) := by
  have h := valid hp hB hBT
  have hLam : 0 < budget p B u := logBudget_pos h.budget_ge hu hu1
  have he : 1 ≤ Real.exp (growth p B * budget p B u) :=
    Real.one_le_exp_iff.mpr (mul_pos (growth_pos hp hB hBT) hLam).le
  have hNp : (1:ℝ) ≤ (N:ℝ)+1 := by have := (Nat.cast_nonneg N : (0:ℝ) ≤ N); linarith
  have hP : 1 ≤ ((N:ℝ)+1)^(p+1) := one_le_pow₀ hNp
  have hN : (N:ℝ) ≤ ((N:ℝ)+1)^(p+1) := by
    exact (by linarith : (N:ℝ) ≤ (N:ℝ)+1).trans (le_self_pow₀ hNp (by omega))
  have hpow : ((N:ℝ)+1)^p ≤ ((N:ℝ)+1)^(p+1) := pow_le_pow_right₀ hNp (by omega)
  have hprep : ((prepareInput p beta J).operations : ℝ) ≤ ((p:ℝ)+14)*((N:ℝ)+1)^p := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using prepareInput_cost (V := Fin N) (by omega : 0<p) beta J)
  have hscan : (scanEvaluations p N B u : ℝ) ≤ N := by exact_mod_cast scanEvaluations_le (N := N) (u := u) hp hB hBT
  have hbase := evaluator_envelope (beta := beta) hp hpN hB hBT hu hu1 J
  have hsetup : ((prepareInput p beta J).operations : ℝ) + 5 + 6 * scanEvaluations p N B u ≤
      ((p:ℝ)+25) * ((N:ℝ)+1)^(p+1) := by
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (p:ℝ)+14 by positivity)
    nlinarith
  rw [execute_operations]
  push_cast
  calc
    _ ≤ ((p:ℝ)+25) * ((N:ℝ)+1)^(p+1) +
        amplitude p B * ((N:ℝ)+1)^(p+1) * Real.exp (growth p B * budget p B u) := add_le_add hsetup hbase
    _ ≤ ((p:ℝ)+25) * ((N:ℝ)+1)^(p+1) * Real.exp (growth p B * budget p B u) +
        amplitude p B * ((N:ℝ)+1)^(p+1) * Real.exp (growth p B * budget p B u) := by
      exact add_le_add (le_mul_of_one_le_right
        (show 0 ≤ ((p:ℝ)+25) * ((N:ℝ)+1)^(p+1) by positivity) he) le_rfl
    _ = _ := by unfold executionAmplitude; ring

/-- Full counted preparation, scan, and evaluation are polynomial uniformly
over all finite real inputs. -/
theorem execution_polynomial {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), p ≤ N → ∀ (beta u : ℝ), 0 < u → u < 1 →
      ∀ J : Finset (Fin N) → ℝ,
      ((execute p N B beta u J).operations : ℝ) ≤ C*(N:ℝ)^C*u^(-C) := by
  let C := envelopeConstant (executionAmplitude p B) (budgetConstant p B) (growth p B) (p+1)
  refine ⟨C, envelopeConstant_pos _ _ _ _, ?_⟩
  intro N hpN beta u hu hu1 J
  have h := valid hp hB hBT
  exact (execution_envelope hp hpN hB hBT hu hu1 J).trans
    (envelope_le_polynomial (by dsimp [executionAmplitude, amplitude]; positivity)
      (by linarith [h.budget_ge]) (by omega) hu hu1.le)

end SpinGlass.HigherOrderAlgorithm
