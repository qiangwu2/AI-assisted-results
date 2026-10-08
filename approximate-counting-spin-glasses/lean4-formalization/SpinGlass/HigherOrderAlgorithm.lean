import SpinGlass.SupportEvaluation
import SpinGlass.DesignConstants
import SpinGlass.BoundedSearch
import SpinGlass.PolynomialRuntime

/-! The actual deterministic higher-order algorithm, with both execution branches. -/

noncomputable section
namespace SpinGlass.HigherOrderAlgorithm
open Finset Real MeasureTheory
open SpinGlass.ArithmeticEvaluation SpinGlass.SupportEvaluation
open SpinGlass.SupportMassBound SpinGlass.SupportMeanSquare
open SpinGlass.DesignConstants SpinGlass.CutoffTail SpinGlass.CutoffSelection
open SpinGlass.AlgorithmBudgets SpinGlass.BoundedSearch SpinGlass.Disorder
open SpinGlass.UniformMass SpinGlass.UniformMassEntropy

def alpha (p : ℕ) (B : ℝ) : ℝ := chosenAlpha (kappa p) (supportScale p B) (aZero p B)
def inflation (p : ℕ) (B : ℝ) : ℝ := (B / inflatedBeta p B)^2
def omega (p : ℕ) (B : ℝ) : ℝ := 2 * alpha p B / p * Real.log (1 / inflation p B)
def rate (p : ℕ) (B : ℝ) : ℝ := nu (kappa p) (supportScale p B) (alpha p B) (omega p B)
def mass (p : ℕ) (B : ℝ) : ℝ := massConstant p ((inflatedBeta p B)^2)
def budgetConstant (p : ℕ) (B : ℝ) : ℝ := 8 * (2 + mass p B)
def sizeLimit (p : ℕ) (B : ℝ) : ℕ := sizeThreshold p (alpha p B)
def budget (p : ℕ) (B u : ℝ) : ℝ := logBudget (budgetConstant p B) u
def exactBranch (p N : ℕ) (B u : ℝ) : Prop := N < sizeLimit p B ∨ rate p B * N ≤ budget p B u
def selectedSize (p N : ℕ) (B u : ℝ) : ℕ :=
  (cutoffScan (kappa p) (supportScale p B) (alpha p B) N (budget p B u)).found.getD 1

/-- The bounded scan chooses the first omitted support. The value computation
then runs one of the two explicitly counted local-spin evaluators. -/
def run (p N : ℕ) (B beta u : ℝ) (J : Finset (Fin N) → ℝ) : Computation := by
  classical
  exact if exactBranch p N B u then
    exactEvaluator p (fun e => weight (pureScale N p beta) (J e))
  else higherEvaluator p (selectedSize p N B u - 1)
    (fun e => weight (pureScale N p beta) (J e))

structure Valid (p : ℕ) (B : ℝ) : Prop where
  alpha_pos : 0 < alpha p B
  alpha_le : alpha p B ≤ 1
  small : aZero p B * (alpha p B)^(p-1) ≤ 1
  gap : 2 ≤ kappa p * (Real.log (1/(supportScale p B * alpha p B))-1)
  inflated : B < inflatedBeta p B
  threshold : (inflatedBeta p B)^2 < thresholdSquared p
  inflation_pos : 0 < inflation p B
  inflation_lt : inflation p B < 1
  omega_pos : 0 < omega p B
  rate_pos : 0 < rate p B
  mass_ge : 1 ≤ mass p B
  budget_ge : 1 ≤ budgetConstant p B

theorem valid {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    Valid p B := by
  have hp0 : 0 < p := by omega
  have hk := kappa_pos hp
  have ha := supportScale_pos p B
  have hK := (aZero_pos hp0 hB).le
  have hap := chosenAlpha_pos (kap := kappa p) ha hK
  have ha1 : alpha p B ≤ 1 := (chosenAlpha_le_eighth _ _ _).trans (by norm_num)
  have hg := chosenAlpha_gap hk ha hK
  have hplus := inflatedBeta_admissible hB hBT
  have hplus0 := hB.trans hplus.1
  have hr0 : 0 < B / inflatedBeta p B := div_pos hB hplus0
  have hr1 : B / inflatedBeta p B < 1 := (div_lt_one hplus0).mpr hplus.1
  have hq0 : 0 < inflation p B := sq_pos_of_pos hr0
  have hq1 : inflation p B < 1 := by dsimp [inflation]; nlinarith
  have how : 0 < omega p B := by
    exact mul_pos (div_pos (mul_pos (by norm_num) hap) (Nat.cast_pos.mpr hp0)) (log_inv_pos hq0 hq1)
  have hmass : 1 ≤ mass p B := one_le_massConstant (sq_nonneg _) hplus.2
  refine ⟨hap, ha1, chosenAlpha_small ha hK (by omega), hg, hplus.1, hplus.2,
    hq0, hq1, how, nu_pos hk ha hap how hg, hmass, ?_⟩
  dsimp [budgetConstant]
  linarith

theorem selectedSize_spec {p N : ℕ} {B u : ℝ} (hp : 3 ≤ p)
    (hB : 0 < B) (hBT : B < betaThreshold p) (hu : 0 < u) (hu1 : u < 1)
    (hnonexact : ¬exactBranch p N B u) :
    1 ≤ selectedSize p N B u ∧ selectedSize p N B u ≤ Nat.floor (alpha p B * N) ∧
      budget p B u ≤ phi (kappa p) (supportScale p B) N (selectedSize p N B u) ∧
        ∀ j : ℕ, 1 ≤ j → j < selectedSize p N B u →
          phi (kappa p) (supportScale p B) N j < budget p B u := by
  have h := valid hp hB hBT
  have hN : sizeLimit p B ≤ N := by unfold exactBranch at hnonexact; omega
  have hsmall : budget p B u < rate p B * N := by
    unfold exactBranch at hnonexact
    push_neg at hnonexact
    exact hnonexact.2
  have hscale : 2 / alpha p B ≤ (N : ℝ) :=
    (sizeThreshold_ge_scale p (alpha p B)).trans (by exact_mod_cast hN)
  obtain ⟨m, hm, hspec⟩ := cutoffScan_correct (kappa_pos hp) (supportScale_pos p B)
    h.alpha_pos h.gap hscale (logBudget_pos h.budget_ge hu hu1) hsmall
  simpa only [selectedSize, budget, hm, Option.getD_some] using hspec

/-- The complete higher-order MSE theorem under the paper's original disorder
assumptions. It has no truncation, selection, or evaluator-correctness premise. -/
theorem mean_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {p N : ℕ} (hp : 3 ≤ p) (hpN : p ≤ N) {B beta u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hu : 0 < u) (hu1 : u < 1) :
    (∫ J : Finset (Fin N) → ℝ,
      ((run p N B beta u J).value -
        SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard p)
          (fun e => pureScale N p beta * J e))^2 ∂iidLaw μ) ≤ u := by
  have h := valid hp hB hBT
  by_cases he : exactBranch p N B u
  · simp only [run, if_pos he, exactEvaluator_disorder_value, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero]
    exact hu.le
  · have hs := selectedSize_spec hp hB hBT hu hu1 he
    have hcut : selectedSize p N B u - 1 < Nat.floor (alpha p B * N) := by omega
    have htail := pure_support_mean_square μ hμ hunit hp hpN hbeta hbetaB hB h.inflated
      h.threshold h.alpha_pos h.alpha_le h.small h.gap hcut
    have hm : selectedSize p N B u - 1 + 1 = selectedSize p N B u := by omega
    have hmR : ((selectedSize p N B u - 1 : ℕ) : ℝ) + 1 = (selectedSize p N B u : ℝ) := by
      exact_mod_cast hm
    have hsmall : budget p B u ≤ rate p B * N := by
      unfold exactBranch at he
      push_neg at he
      exact he.2.le
    have herrors := selected_error_bounds (Nat.cast_nonneg N : (0:ℝ) ≤ N)
      (logBudget_pos h.budget_ge hu hu1).le hsmall hs.2.2.1
    have hmass : 0 ≤ mass p B := le_trans zero_le_one h.mass_ge
    calc
      _ = ∫ J : Finset (Fin N) → ℝ,
          (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard p)
            (fun e => pureScale N p beta * J e) -
            supportApproximation p (selectedSize p N B u - 1) (pureScale N p beta) J)^2 ∂iidLaw μ := by
        apply integral_congr_ae
        filter_upwards [] with J
        simp only [run, if_neg he, higherEvaluator_disorder_value]
        ring
      _ ≤ 2 * Real.exp (-phi (kappa p) (supportScale p B) N (selectedSize p N B u)) +
          mass p B * Real.exp (-omega p B * N) := by simpa only [hmR, mass, omega, inflation] using htail
      _ ≤ 2 * Real.exp (-budget p B u) + mass p B * Real.exp (-4 * budget p B u) := by
        exact add_le_add (mul_le_mul_of_nonneg_left herrors.1 (by norm_num))
          (mul_le_mul_of_nonneg_left herrors.2 hmass)
      _ ≤ u := support_error_budget hmass hu hu1

end SpinGlass.HigherOrderAlgorithm
