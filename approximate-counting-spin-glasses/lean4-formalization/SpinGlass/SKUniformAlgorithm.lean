import SpinGlass.SKRandomMeanSquare
import SpinGlass.DesignConstants
import SpinGlass.BoundedSearch
import SpinGlass.AlgorithmBudgets
import SpinGlass.Threshold

/-! Automatic SK cutoffs and the exact branch, with uniform actual joint MSE.
The graph-sum value is connected to the concrete fast evaluator separately. -/
noncomputable section
namespace SpinGlass.SKUniformAlgorithm
open MeasureTheory Finset Real
open SpinGlass.DesignConstants SpinGlass.CutoffTail SpinGlass.CutoffSelection
open SpinGlass.AlgorithmBudgets SpinGlass.BoundedSearch SpinGlass.Disorder
open SpinGlass.UniformMassEntropy

def branchScale (B : ℝ) : ℝ := max 1 (SpinGlass.SKBranchingScalar.branchConstant B)
def alpha (B : ℝ) : ℝ := chosenAlpha 1 (branchScale B) 0
def inflation (B : ℝ) : ℝ := (B / inflatedBeta 2 B) ^ 2
def omega (B : ℝ) : ℝ := 2 * alpha B * Real.log (1 / inflation B)
def rate (B : ℝ) : ℝ := nu 1 (branchScale B) (alpha B) (omega B)
def mass (B : ℝ) : ℝ := SpinGlass.UniformMass.massConstant 2 ((inflatedBeta 2 B) ^ 2)
def branchMass (B : ℝ) : ℝ := SpinGlass.SKBranchingScalar.massConstant B
def budgetConstant (B : ℝ) : ℝ := 8 * (2 * branchMass B + 3 * mass B)
def budget (B u : ℝ) : ℝ := logBudget (budgetConstant B) u
def sizeLimit (B : ℝ) : ℕ := sizeThreshold 2 (alpha B)
def exactBranch (N : ℕ) (B u : ℝ) : Prop := N < sizeLimit B ∨ rate B * N ≤ budget B u
def selectedSize (N : ℕ) (B u : ℝ) : ℕ :=
  (cutoffScan 1 (branchScale B) (alpha B) N (budget B u)).found.getD 1
def edgeLimit (B u : ℝ) : ℕ := edgeCutoff (inflation B) (budget B u)
def repetitions (B u : ℝ) : ℕ := colorTrials (edgeLimit B u) (budget B u)
abbrev Randomness (N : ℕ) (B u : ℝ) :=
  SpinGlass.SKRandomMeanSquare.Colors (Fin N) (edgeLimit B u) (repetitions B u)

def randomLaw (N : ℕ) (B u : ℝ) : Measure (Randomness N B u) :=
  SpinGlass.SKRandomMeanSquare.colorLaw (Fin N) (edgeLimit B u) (repetitions B u)

/-- The complete graph-sum procedure includes exact enumeration when the size or
requested accuracy puts the input in the exact branch. -/
def run (N : ℕ) (B beta u : ℝ) (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) : ℝ := by
  classical
  exact if exactBranch N B u then
    SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard 2)
      (fun e => pureScale N 2 beta * J e)
  else SpinGlass.SKRandomMeanSquare.estimator (selectedSize N B u - 1)
    (edgeLimit B u) (repetitions B u) (pureScale N 2 beta) χ J

structure Valid (B : ℝ) : Prop where
  B_lt_one : B < 1
  alpha_pos : 0 < alpha B
  alpha_le : alpha B ≤ 1
  scale_pos : 0 < branchScale B
  gap : 2 ≤ Real.log (1 / (branchScale B * alpha B)) - 1
  inflated : B < inflatedBeta 2 B
  threshold : (inflatedBeta 2 B) ^ 2 < thresholdSquared 2
  inflation_pos : 0 < inflation B
  inflation_lt : inflation B < 1
  omega_pos : 0 < omega B
  rate_pos : 0 < rate B
  mass_ge : 1 ≤ mass B
  branchMass_ge : 1 ≤ branchMass B
  budget_ge : 1 ≤ budgetConstant B

/-- All design constants are explicit and admissible under exactly B<β₂=1. -/
theorem valid {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) : Valid B := by
  have hB1 : B < 1 := by
    simpa [betaThreshold, SpinGlass.Threshold.thresholdSquared_two] using hBT
  have ha : 0 < branchScale B := zero_lt_one.trans_le (le_max_left _ _)
  have hap : 0 < alpha B := chosenAlpha_pos (kap := 1) ha (by norm_num)
  have ha1 : alpha B ≤ 1 := (chosenAlpha_le_eighth _ _ _).trans (by norm_num)
  have hg : 2 ≤ Real.log (1 / (branchScale B * alpha B)) - 1 := by
    simpa [alpha] using chosenAlpha_gap (by norm_num : (0 : ℝ) < 1) ha (by norm_num : (0 : ℝ) ≤ 0)
  have hplus := inflatedBeta_admissible hB hBT
  have hplus0 := hB.trans hplus.1
  have hr0 : 0 < B / inflatedBeta 2 B := div_pos hB hplus0
  have hr1 : B / inflatedBeta 2 B < 1 := (div_lt_one hplus0).mpr hplus.1
  have hq0 : 0 < inflation B := sq_pos_of_pos hr0
  have hq1 : inflation B < 1 := by dsimp [inflation]; nlinarith
  have how : 0 < omega B := mul_pos (mul_pos (by norm_num) hap) (log_inv_pos hq0 hq1)
  have hmass : 1 ≤ mass B := SpinGlass.UniformMass.one_le_massConstant (sq_nonneg _) hplus.2
  have hbranch : 1 ≤ branchMass B := SpinGlass.SKBranchingScalar.massConstant_ge_one hB.le hB1
  refine ⟨hB1, hap, ha1, ha, hg, hplus.1, hplus.2, hq0, hq1, how,
    nu_pos (by norm_num) ha hap how (by simpa using hg), hmass, hbranch, ?_⟩
  dsimp [budgetConstant]
  linarith

theorem edgeLimit_pos {B u : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2)
    (hu : 0 < u) (hu1 : u < 1) : 0 < edgeLimit B u := by
  have h := valid hB hBT
  exact edgeCutoff_pos h.inflation_pos h.inflation_lt (logBudget_pos h.budget_ge hu hu1)

theorem repetitions_pos (B u : ℝ) : 0 < repetitions B u := colorTrials_pos _ _

theorem randomLaw_probability {N : ℕ} {B u : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2)
    (hu : 0 < u) (hu1 : u < 1) : IsProbabilityMeasure (randomLaw N B u) := by
  letI : Nonempty (Fin (edgeLimit B u)) := ⟨⟨0, edgeLimit_pos hB hBT hu hu1⟩⟩
  unfold randomLaw
  infer_instance

/-- The literal bounded scan chooses the first omitted branching size. -/
theorem selectedSize_spec {N : ℕ} {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (hnonexact : ¬exactBranch N B u) :
    1 ≤ selectedSize N B u ∧ selectedSize N B u ≤ Nat.floor (alpha B * N) ∧
      budget B u ≤ phi 1 (branchScale B) N (selectedSize N B u) ∧
        ∀ j : ℕ, 1 ≤ j → j < selectedSize N B u → phi 1 (branchScale B) N j < budget B u := by
  have h := valid hB hBT
  have hN : sizeLimit B ≤ N := by unfold exactBranch at hnonexact; omega
  have hsmall : budget B u < rate B * N := by
    unfold exactBranch at hnonexact
    push Not at hnonexact
    exact hnonexact.2
  have hscale : 2 / alpha B ≤ (N : ℝ) :=
    (sizeThreshold_ge_scale 2 (alpha B)).trans (by exact_mod_cast hN)
  obtain ⟨m, hm, hspec⟩ := cutoffScan_correct (by norm_num : (0 : ℝ) < 1) h.scale_pos
    h.alpha_pos (by simpa using h.gap) hscale (logBudget_pos h.budget_ge hu hu1) hsmall
  simpa only [selectedSize, budget, hm, Option.getD_some] using hspec

/-- Integrability of the full automatic algorithm's actual product-law error. -/
theorem error_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] {N : ℕ} {B beta u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1) :
    Integrable (fun χJ : Randomness N B u × (Finset (Fin N) → ℝ) =>
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard 2)
        (fun e => pureScale N 2 beta * χJ.2 e) - run N B beta u χJ.1 χJ.2) ^ 2)
      ((randomLaw N B u).prod (iidLaw μ)) := by
  by_cases he : exactBranch N B u
  · simp only [run, if_pos he, sub_self, zero_pow (by omega : 2 ≠ 0)]
    exact integrable_zero _ _ _
  · simp only [run, if_neg he]
    exact SpinGlass.SKRandomMeanSquare.error_integrable μ _ (edgeLimit_pos hB hBT hu hu1) _

/-- Uniform MSE of the automatic SK estimator under the paper's original
symmetric variance-one iid law. The cutoffs and exact branch are derived. -/
theorem mean_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N : ℕ} (hN : 2 ≤ N)
    {B beta u : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hu : 0 < u) (hu1 : u < 1) :
    (∫ χJ : Randomness N B u × (Finset (Fin N) → ℝ),
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard 2)
        (fun e => pureScale N 2 beta * χJ.2 e) - run N B beta u χJ.1 χJ.2) ^ 2
      ∂(randomLaw N B u).prod (iidLaw μ)) ≤ u := by
  have h := valid hB hBT
  by_cases he : exactBranch N B u
  · simp only [run, if_pos he, sub_self, zero_pow (by omega : 2 ≠ 0), integral_zero]
    exact hu.le
  · have hs := selectedSize_spec hB hBT hu hu1 he
    have hcut : selectedSize N B u - 1 < Nat.floor (alpha B * N) := by omega
    have hm : selectedSize N B u - 1 + 1 = selectedSize N B u := by omega
    have hmR : ((selectedSize N B u - 1 : ℕ) : ℝ) + 1 = (selectedSize N B u : ℝ) := by exact_mod_cast hm
    have hsmall : budget B u ≤ rate B * N := by
      unfold exactBranch at he
      push Not at he
      exact he.2.le
    have hLam := logBudget_pos h.budget_ge hu hu1
    have herrors := selected_error_bounds (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hLam.le hsmall hs.2.2.1
    have hmass : 0 < mass B := zero_lt_one.trans_le h.mass_ge
    have hbranch : 0 ≤ branchMass B := zero_le_one.trans h.branchMass_ge
    have htail := SpinGlass.SKRandomMeanSquare.physical_mse_four_terms μ hμ hunit hN
      (edgeLimit_pos hB hBT hu hu1) (repetitions_pos B u) hbeta hbetaB hB h.B_lt_one h.inflated
      h.threshold h.alpha_pos h.gap hcut
    simp only [run, if_neg he]
    calc
      _ ≤ mass B * inflation B ^ (edgeLimit B u + 1) +
          2 * branchMass B * Real.exp (-phi 1 (branchScale B) N (selectedSize N B u)) +
          mass B * Real.exp (-omega B * N) + mass B * (Real.exp (edgeLimit B u : ℝ) / repetitions B u) := by
        simpa only [randomLaw, hmR, mass, branchMass, branchScale, omega, inflation] using htail
      _ ≤ mass B * Real.exp (-budget B u) + 2 * branchMass B * Real.exp (-budget B u) +
          mass B * Real.exp (-4 * budget B u) + mass B * Real.exp (-budget B u) := by
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (edgeCutoff_error h.inflation_pos h.inflation_lt hLam.le) hmass.le)
          (mul_le_mul_of_nonneg_left herrors.1 (by positivity)))
          (mul_le_mul_of_nonneg_left herrors.2 hmass.le))
          (mul_le_mul_of_nonneg_left (colorTrials_error (edgeLimit B u) (budget B u)) hmass.le)
      _ ≤ u := sk_error_budget hmass hbranch hu hu1 h.budget_ge

end SpinGlass.SKUniformAlgorithm
