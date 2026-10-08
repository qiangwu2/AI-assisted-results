import SpinGlass.AccuracyRuntime

/-! # Polynomial confidence schedules and their actual runtime substitution -/
noncomputable section
namespace SpinGlass.ConfidenceSchedules
open Real

/-- One schedule serves both typical-instance confidence and a prescribed power. -/
def delta (N : ℕ) (b : ℝ) : ℝ := (1/2) * (N : ℝ)^(-b)

theorem delta_pos {N : ℕ} (hN : 0 < N) (b : ℝ) : 0 < delta N b := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold delta
  positivity

theorem delta_le_half {N : ℕ} (hN : 1 ≤ N) {b : ℝ} (hb : 0 ≤ b) : delta N b ≤ 1/2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ)^(-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  unfold delta
  nlinarith

theorem delta_lt_one {N : ℕ} (hN : 1 ≤ N) {b : ℝ} (hb : 0 ≤ b) : delta N b < 1 :=
  (delta_le_half hN hb).trans_lt (by norm_num)

theorem inverse_delta {N : ℕ} (hN : 0 < N) (b C : ℝ) :
    (delta N b)^(-C) = (2 : ℝ)^C * (N : ℝ)^(b*C) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := delta_pos hN b
  rw [Real.rpow_def_of_pos hd, delta,
    Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hNR _).ne',
    Real.log_rpow hNR, Real.log_div (by norm_num) (by norm_num), Real.log_one,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hNR,
    ← Real.exp_add]
  congr 1
  ring

def runtimeConstant (C b : ℝ) : ℝ := max 1 (max C (max ((1+b)*C) (C*(2:ℝ)^C)))

theorem runtimeConstant_pos (C b : ℝ) : 0 < runtimeConstant C b :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Substituting polynomial confidence leaves a fixed polynomial in N and
inverse requested accuracy, with no dependence of its exponent on accuracy. -/
theorem runtime_substitution {N : ℕ} (hN : 1 ≤ N) {C epsilon : ℝ} (hC : 0 ≤ C)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1) (b : ℝ) :
    C*(N:ℝ)^C*epsilon^(-C)*(delta N b)^(-C) ≤
      runtimeConstant C b * (N:ℝ)^(runtimeConstant C b) * epsilon^(-runtimeConstant C b) := by
  let D := runtimeConstant C b
  have hD := runtimeConstant_pos C b
  have hNC : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hNC
  have hCD : C ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hND : (1+b)*C ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcoeff : C*(2:ℝ)^C ≤ D :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow : (N:ℝ)^C * (N:ℝ)^(b*C) = (N:ℝ)^((1+b)*C) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  rw [inverse_delta (by omega : 0 < N)]
  calc
    _ = (C*(2:ℝ)^C) * ((N:ℝ)^C*(N:ℝ)^(b*C)) * epsilon^(-C) := by ring
    _ = (C*(2:ℝ)^C) * (N:ℝ)^((1+b)*C) * epsilon^(-C) := by rw [hpow]
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul hcoeff (Real.rpow_le_rpow_of_exponent_le hNC hND)
          (Real.rpow_nonneg hN0.le _) hD.le
      · exact Real.rpow_le_rpow_of_exponent_ge he he1 (neg_le_neg hCD)
      · positivity
      · positivity

end SpinGlass.ConfidenceSchedules
