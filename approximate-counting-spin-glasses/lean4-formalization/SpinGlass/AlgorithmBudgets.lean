import SpinGlass.CutoffSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The exact integer edge cutoff, number of color trials, and accuracy budgets. -/

noncomputable section
namespace SpinGlass.AlgorithmBudgets
open Real

def edgeCutoff (q Lambda : ℝ) : ℕ := Nat.ceil (Lambda / Real.log (1 / q))
def colorTrials (L : ℕ) (Lambda : ℝ) : ℕ := Nat.ceil (Real.exp ((L : ℝ) + Lambda))
def logBudget (H u : ℝ) : ℝ := Real.log (H / u)

theorem log_inv_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : 0 < Real.log (1 / q) := by
  apply Real.log_pos
  exact (lt_div_iff₀ hq).2 (by simpa using hq1)

theorem edgeCutoff_pos {q Lambda : ℝ} (hq : 0 < q) (hq1 : q < 1) (hLam : 0 < Lambda) :
    1 ≤ edgeCutoff q Lambda :=
  Nat.one_le_ceil_iff.mpr (div_pos hLam (log_inv_pos hq hq1))

theorem edgeCutoff_le {q Lambda : ℝ} (hq : 0 < q) (hq1 : q < 1) (hLam : 0 ≤ Lambda) :
    (edgeCutoff q Lambda : ℝ) ≤ Lambda / Real.log (1 / q) + 1 :=
  (Nat.ceil_lt_add_one (div_nonneg hLam (log_inv_pos hq hq1).le)).le

theorem edgeCutoff_error {q Lambda : ℝ} (hq : 0 < q) (hq1 : q < 1) (hLam : 0 ≤ Lambda) :
    q ^ (edgeCutoff q Lambda + 1) ≤ Real.exp (-Lambda) := by
  have hd := log_inv_pos hq hq1
  have hL : Lambda ≤ (edgeCutoff q Lambda : ℝ) * Real.log (1 / q) :=
    (div_le_iff₀ hd).mp (Nat.le_ceil _)
  have hlog : Real.log (1 / q) = -Real.log q := by simp [one_div]
  have hrepr : q ^ (edgeCutoff q Lambda + 1) =
      Real.exp (((edgeCutoff q Lambda : ℝ) + 1) * Real.log q) := by
    rw [show (edgeCutoff q Lambda : ℝ) + 1 = ((edgeCutoff q Lambda + 1 : ℕ) : ℝ) by simp,
      Real.exp_nat_mul, Real.exp_log hq]
  rw [hrepr]
  rw [hlog] at hd hL
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem colorTrials_pos (L : ℕ) (Lambda : ℝ) : 0 < colorTrials L Lambda :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem colorTrials_error (L : ℕ) (Lambda : ℝ) :
    Real.exp L / colorTrials L Lambda ≤ Real.exp (-Lambda) := by
  have hR : 0 < (colorTrials L Lambda : ℝ) := Nat.cast_pos.mpr (colorTrials_pos _ _)
  apply (div_le_iff₀ hR).2
  have h := mul_le_mul_of_nonneg_left (Nat.le_ceil (Real.exp ((L : ℝ) + Lambda)))
    (Real.exp_pos (-Lambda)).le
  have heq : Real.exp (-Lambda) * Real.exp ((L : ℝ) + Lambda) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [heq, colorTrials] using h

theorem colorTrials_le (L : ℕ) {Lambda : ℝ} (hLam : 0 ≤ Lambda) :
    (colorTrials L Lambda : ℝ) ≤ 2 * Real.exp ((L : ℝ) + Lambda) := by
  have h := Nat.ceil_lt_add_one (Real.exp_pos ((L : ℝ) + Lambda)).le
  have he : 1 ≤ Real.exp ((L : ℝ) + Lambda) := Real.one_le_exp_iff.mpr (by positivity)
  dsimp [colorTrials]
  linarith

theorem logBudget_pos {H u : ℝ} (hH : 1 ≤ H) (hu : 0 < u) (hu1 : u < 1) :
    0 < logBudget H u := by
  apply Real.log_pos
  exact (lt_div_iff₀ hu).2 (by linarith)

theorem exp_neg_logBudget {H u : ℝ} (hH : 0 < H) (hu : 0 < u) :
    Real.exp (-logBudget H u) = u / H := by
  rw [logBudget, Real.exp_neg, Real.exp_log (div_pos hH hu), inv_div]

theorem exp_four_le_exp {Lambda : ℝ} (hLam : 0 ≤ Lambda) :
    Real.exp (-4 * Lambda) ≤ Real.exp (-Lambda) :=
  Real.exp_le_exp.mpr (by linarith)

theorem support_error_budget {C u : ℝ} (hC : 0 ≤ C) (hu : 0 < u) (hu1 : u < 1) :
    2 * Real.exp (-logBudget (8 * (2 + C)) u) +
      C * Real.exp (-4 * logBudget (8 * (2 + C)) u) ≤ u := by
  have hH : 0 < 8 * (2 + C) := by positivity
  have hLam := logBudget_pos (by linarith : 1 ≤ 8 * (2 + C)) hu hu1
  calc
    _ ≤ (2 + C) * Real.exp (-logBudget (8 * (2 + C)) u) := by
      have h := mul_le_mul_of_nonneg_left (exp_four_le_exp hLam.le) hC
      nlinarith
    _ = u / 8 := by rw [exp_neg_logBudget hH hu]; field_simp
    _ ≤ u := by linarith

theorem sk_error_budget {C CB u : ℝ} (hC : 0 < C) (hCB : 0 ≤ CB)
    (hu : 0 < u) (hu1 : u < 1) (hH : 1 ≤ 8 * (2 * CB + 3 * C)) :
    C * Real.exp (-logBudget (8 * (2 * CB + 3 * C)) u) +
      2 * CB * Real.exp (-logBudget (8 * (2 * CB + 3 * C)) u) +
      C * Real.exp (-4 * logBudget (8 * (2 * CB + 3 * C)) u) +
      C * Real.exp (-logBudget (8 * (2 * CB + 3 * C)) u) ≤ u := by
  have hHpos : 0 < 8 * (2 * CB + 3 * C) := by positivity
  have hLam := logBudget_pos hH hu hu1
  calc
    _ ≤ (2 * CB + 3 * C) * Real.exp (-logBudget (8 * (2 * CB + 3 * C)) u) := by
      have h := mul_le_mul_of_nonneg_left (exp_four_le_exp hLam.le) hC.le
      nlinarith
    _ = u / 8 := by rw [exp_neg_logBudget hHpos hu]; field_simp
    _ ≤ u := by linarith

/-- The logarithmic budget really has polynomial dependence on the input
accuracy, with fixed real exponents. -/
theorem exp_logBudget {H u c : ℝ} (hH : 0 < H) (hu : 0 < u) :
    Real.exp (c * logBudget H u) = H ^ c * u ^ (-c) := by
  rw [logBudget, Real.log_div hH.ne' hu.ne', Real.rpow_def_of_pos hH,
    Real.rpow_def_of_pos hu, ← Real.exp_add]
  congr 1
  ring

theorem exact_branch_cost {nu Lambda : ℝ} {N : ℕ} (hnu : 0 < nu)
    (hlarge : nu * N ≤ Lambda) :
    (2 : ℝ)^N ≤ Real.exp ((Real.log 2 / nu) * Lambda) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hN : (N : ℝ) ≤ Lambda / nu := (le_div_iff₀ hnu).2 (by nlinarith)
  have heq : (2 : ℝ)^N = Real.exp ((N : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [heq]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hN hlog
  convert h using 1 <;> first | rfl | ring

end SpinGlass.AlgorithmBudgets
