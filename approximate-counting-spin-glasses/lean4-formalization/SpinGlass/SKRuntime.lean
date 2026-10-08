import SpinGlass.SKUniformAlgorithm
import SpinGlass.PolynomialRuntime

/-! # Uniform polynomial envelope for the automatic SK arithmetic schedule -/
noncomputable section
namespace SpinGlass.SKUniformAlgorithm
open Finset Real
open SpinGlass.DesignConstants SpinGlass.CutoffSelection SpinGlass.AlgorithmBudgets
open SpinGlass.PolynomialRuntime

def candidateGrowth (B : ℝ) : ℝ := costConstant 1 (branchScale B) (alpha B) 36
def colorGrowth (B : ℝ) : ℝ :=
  1 + (1 + Real.log 4) / Real.log (1 / inflation B) + candidateGrowth B
def growth (B : ℝ) : ℝ := max (colorGrowth B) (Real.log 2 / rate B)
def sizeFactor (B : ℝ) : ℝ := 2 + rate B / Real.log (1 / inflation B)
def colorAmplitude (B : ℝ) : ℝ := (sizeFactor B)^4 * (2 * Real.exp (1 + Real.log 4))
def amplitude (B : ℝ) : ℝ := 8 * (2 : ℝ)^(sizeLimit B) + 64 * colorAmplitude B

/-- Literal binomial/color factor in the scheduled SK evaluator bound. -/
def approximateWork (N : ℕ) (B u : ℝ) : ℝ :=
  (repetitions B u : ℝ) * ((N : ℝ) + edgeLimit B u + 1)^4 * (4 : ℝ)^(edgeLimit B u) *
    ∑ j ∈ Finset.range (selectedSize N B u), (N.choose j : ℝ) * (36 : ℝ)^j

theorem growth_pos {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) : 0 < growth B := by
  have h := valid hB hBT
  have hc : 0 < candidateGrowth B :=
    costConstant_pos (by norm_num) (le_max_left _ _) (by norm_num) (by simpa using h.gap)
  have hlog : 0 < Real.log (1 / inflation B) := log_inv_pos h.inflation_pos h.inflation_lt
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcolor : 0 < colorGrowth B := by unfold colorGrowth; positivity
  exact hcolor.trans_le (le_max_left _ _)

theorem sizeFactor_pos {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) : 0 < sizeFactor B := by
  have h := valid hB hBT
  have hlog : 0 < Real.log (1 / inflation B) := log_inv_pos h.inflation_pos h.inflation_lt
  unfold sizeFactor
  exact add_pos (by norm_num) (div_pos h.rate_pos hlog)

theorem colorAmplitude_pos {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    0 < colorAmplitude B := by
  have h := sizeFactor_pos hB hBT
  unfold colorAmplitude
  positivity

theorem amplitude_ge_exact {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    8 * (2 : ℝ)^(sizeLimit B) ≤ amplitude B := by
  have h := colorAmplitude_pos hB hBT
  unfold amplitude
  linarith

theorem amplitude_ge_color {B : ℝ} : 64 * colorAmplitude B ≤ amplitude B := by
  unfold amplitude
  have h : 0 < (2 : ℝ)^(sizeLimit B) := by positivity
  linarith

/-- Minimality of the bounded scan controls the entire retained candidate sum. -/
theorem candidate_sum_bound {N : ℕ} (hN : 2 ≤ N) {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (he : ¬exactBranch N B u) :
    (∑ j ∈ Finset.range (selectedSize N B u), (N.choose j : ℝ) * (36 : ℝ)^j) ≤
      ((N : ℝ)+1) * Real.exp (candidateGrowth B * budget B u) := by
  have h := valid hB hBT
  have hs := selectedSize_spec hB hBT hu hu1 he
  exact selected_binomial_cost (by norm_num) (le_max_left _ _) h.alpha_pos h.alpha_le
    (by norm_num) (by simpa using h.gap) (by omega)
    (logBudget_pos h.budget_ge hu hu1).le hs.2.1 hs.2.2.2

/-- The full actual color/repetition/candidate factor is uniformly exponential
only in the logarithmic error budget. -/
theorem approximate_envelope {N : ℕ} (hN : 2 ≤ N) {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (he : ¬exactBranch N B u) :
    approximateWork N B u ≤ colorAmplitude B * ((N : ℝ)+1)^5 *
      Real.exp (growth B * budget B u) := by
  have h := valid hB hBT
  have hLam := logBudget_pos h.budget_ge hu hu1
  have hsmall : budget B u ≤ rate B * N := by
    unfold exactBranch at he
    push Not at he
    exact he.2.le
  have hsize := sk_size_factor h.inflation_pos h.inflation_lt hLam.le h.rate_pos.le hsmall
  have hcolor := sk_color_factor (c := candidateGrowth B)
    h.inflation_pos h.inflation_lt hLam.le
  have hsum := candidate_sum_bound hN hB hBT hu hu1 he
  have hsf := sizeFactor_pos hB hBT
  calc
    approximateWork N B u ≤
        (repetitions B u : ℝ) * (sizeFactor B * ((N : ℝ)+1))^4 * (4 : ℝ)^(edgeLimit B u) *
          (((N : ℝ)+1) * Real.exp (candidateGrowth B * budget B u)) := by
      unfold approximateWork
      gcongr
      exact hsize
    _ = (sizeFactor B)^4 * ((N : ℝ)+1)^5 *
        ((repetitions B u : ℝ) * (4 : ℝ)^(edgeLimit B u) *
          Real.exp (candidateGrowth B * budget B u)) := by ring
    _ ≤ (sizeFactor B)^4 * ((N : ℝ)+1)^5 *
        ((2 * Real.exp (1 + Real.log 4)) * Real.exp (colorGrowth B * budget B u)) := by
      exact mul_le_mul_of_nonneg_left hcolor (by positivity)
    _ = colorAmplitude B * ((N : ℝ)+1)^5 * Real.exp (colorGrowth B * budget B u) := by
      unfold colorAmplitude
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have := colorAmplitude_pos hB hBT; positivity)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hLam.le)

/-- Additional fixed polynomial control work is absorbed with the same accuracy
exponent. This version covers any explicitly proved schedule power. -/
theorem approximate_envelope_power (d : ℕ) {N : ℕ} (hN : 2 ≤ N) {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (he : ¬exactBranch N B u) :
    (repetitions B u : ℝ) * ((N : ℝ) + edgeLimit B u + 1)^d * (4 : ℝ)^(edgeLimit B u) *
      (∑ j ∈ Finset.range (selectedSize N B u), (N.choose j : ℝ) * (36 : ℝ)^j) ≤
      ((sizeFactor B)^d * (2 * Real.exp (1 + Real.log 4))) * ((N : ℝ)+1)^(d+1) *
        Real.exp (growth B * budget B u) := by
  have h := valid hB hBT
  have hLam := logBudget_pos h.budget_ge hu hu1
  have hsmall : budget B u ≤ rate B * N := by
    unfold exactBranch at he
    push Not at he
    exact he.2.le
  have hsize := sk_size_factor h.inflation_pos h.inflation_lt hLam.le h.rate_pos.le hsmall
  have hcolor := sk_color_factor (c := candidateGrowth B)
    h.inflation_pos h.inflation_lt hLam.le
  have hsum := candidate_sum_bound hN hB hBT hu hu1 he
  have hsf := sizeFactor_pos hB hBT
  calc
    _ ≤ (repetitions B u : ℝ) * (sizeFactor B * ((N : ℝ)+1))^d * (4 : ℝ)^(edgeLimit B u) *
          (((N : ℝ)+1) * Real.exp (candidateGrowth B * budget B u)) := by
      gcongr
      exact hsize
    _ = (sizeFactor B)^d * ((N : ℝ)+1)^(d+1) *
        ((repetitions B u : ℝ) * (4 : ℝ)^(edgeLimit B u) *
          Real.exp (candidateGrowth B * budget B u)) := by rw [mul_pow,pow_succ]; ring
    _ ≤ (sizeFactor B)^d * ((N : ℝ)+1)^(d+1) *
        ((2 * Real.exp (1 + Real.log 4)) * Real.exp (colorGrowth B * budget B u)) := by
      exact mul_le_mul_of_nonneg_left hcolor (by positivity)
    _ = ((sizeFactor B)^d * (2 * Real.exp (1 + Real.log 4))) * ((N : ℝ)+1)^(d+1) *
        Real.exp (colorGrowth B * budget B u) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hLam.le)

/-- The exact branch also fits the same uniform envelope, including the finite
small-size range where direct enumeration is used. -/
theorem exact_envelope {N : ℕ} (hN : 2 ≤ N) {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hu : 0 < u) (hu1 : u < 1)
    (he : exactBranch N B u) :
    8 * ((N : ℝ)+1)^2 * (2 : ℝ)^N ≤
      amplitude B * ((N : ℝ)+1)^5 * Real.exp (growth B * budget B u) := by
  have h := valid hB hBT
  have hLam := logBudget_pos h.budget_ge hu hu1
  have hexp : 1 ≤ Real.exp (growth B * budget B u) :=
    Real.one_le_exp_iff.mpr (mul_pos (growth_pos hB hBT) hLam).le
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsize : ((N : ℝ)+1)^2 ≤ ((N : ℝ)+1)^5 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hA := amplitude_ge_exact hB hBT
  have h2 : (1 : ℝ) ≤ (2 : ℝ)^(sizeLimit B) := one_le_pow₀ (by norm_num)
  have hA8 : 8 ≤ amplitude B := by nlinarith
  rcases he with hsmall | hlarge
  · have hpow : (2 : ℝ)^N ≤ (2 : ℝ)^(sizeLimit B) :=
      pow_le_pow_right₀ (by norm_num) hsmall.le
    calc
      _ ≤ 8 * ((N : ℝ)+1)^5 * (2 : ℝ)^(sizeLimit B) := by gcongr
      _ = (8 * (2 : ℝ)^(sizeLimit B)) * ((N : ℝ)+1)^5 := by ring
      _ ≤ amplitude B * ((N : ℝ)+1)^5 := mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hexp
  · have hpow := exact_branch_cost h.rate_pos hlarge
    have hpow' : (2 : ℝ)^N ≤ Real.exp (growth B * budget B u) :=
      hpow.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hLam.le))
    exact mul_le_mul (mul_le_mul_of_nonneg_right hA8 (by positivity) |>.trans
      (mul_le_mul_of_nonneg_left hsize (by linarith))) hpow' (by positivity) (by positivity)

end SpinGlass.SKUniformAlgorithm
