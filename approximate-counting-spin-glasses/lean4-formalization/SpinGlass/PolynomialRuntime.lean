import SpinGlass.AlgorithmBudgets

/-! Converting the explicit arithmetic counts into the stated uniform polynomial. -/

noncomputable section
namespace SpinGlass.PolynomialRuntime
open Real
open SpinGlass.AlgorithmBudgets

def envelopeConstant (A H c : ℝ) (d : ℕ) : ℝ :=
  max 1 (max (d : ℝ) (max c (A * H^c * (2 : ℝ)^d)))

theorem envelopeConstant_pos (A H c : ℝ) (d : ℕ) : 0 < envelopeConstant A H c d :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- The same exponent controls the polynomial coefficient, the input size,
and inverse accuracy. All constants are fixed independently of `N,u`. -/
theorem envelope_le_polynomial {A H c : ℝ} {d N : ℕ} {u : ℝ}
    (hA : 0 ≤ A) (hH : 0 < H) (hN : 1 ≤ N) (hu : 0 < u) (hu1 : u ≤ 1) :
    A * ((N : ℝ) + 1)^d * Real.exp (c * logBudget H u) ≤
      envelopeConstant A H c d * (N : ℝ)^(envelopeConstant A H c d) *
        u^(-envelopeConstant A H c d) := by
  let C := envelopeConstant A H c d
  have hC0 : 0 < C := envelopeConstant_pos _ _ _ _
  have hd : (d : ℝ) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hc : c ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcoef : A * H^c * (2 : ℝ)^d ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsize : ((N : ℝ) + 1)^d ≤ (2 : ℝ)^d * (N : ℝ)^d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpow : (N : ℝ)^d ≤ (N : ℝ)^C := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hd
  have huPow : u^(-c) ≤ u^(-C) :=
    Real.rpow_le_rpow_of_exponent_ge hu hu1 (neg_le_neg hc)
  rw [exp_logBudget hH hu]
  calc
    A * ((N : ℝ) + 1)^d * (H^c * u^(-c)) ≤
        A * ((2 : ℝ)^d * (N : ℝ)^d) * (H^c * u^(-c)) := by
      gcongr
    _ = (A * H^c * (2 : ℝ)^d) * (N : ℝ)^d * u^(-c) := by ring
    _ ≤ C * (N : ℝ)^C * u^(-C) := by
      apply mul_le_mul
      · exact mul_le_mul hcoef hpow (pow_nonneg hN0 _) hC0.le
      · exact huPow
      · exact (Real.rpow_pos_of_pos hu _).le
      · exact mul_nonneg hC0.le (Real.rpow_nonneg hN0 _)

/-- The ceiling choices in SK contribute only a fixed exponential in the
logarithmic error budget. This includes the repetitions and `4^L`. -/
theorem sk_color_factor {q Lambda c : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hLam : 0 ≤ Lambda) :
    (colorTrials (edgeCutoff q Lambda) Lambda : ℝ) *
      (4 : ℝ)^(edgeCutoff q Lambda) * Real.exp (c * Lambda) ≤
      (2 * Real.exp (1 + Real.log 4)) *
        Real.exp ((1 + (1 + Real.log 4) / Real.log (1/q) + c) * Lambda) := by
  let L := edgeCutoff q Lambda
  have hL := edgeCutoff_le hq hq1 hLam
  have hR := colorTrials_le L hLam
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h4 : (4 : ℝ)^L = Real.exp ((L : ℝ) * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  calc
    _ ≤ (2 * Real.exp ((L : ℝ) + Lambda)) * (4 : ℝ)^L * Real.exp (c * Lambda) := by
      gcongr
    _ = 2 * Real.exp (((1 + Real.log 4) * L) + (1 + c) * Lambda) := by
      rw [h4]
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 2 * Real.exp ((1 + Real.log 4) * (Lambda / Real.log (1/q) + 1) +
        (1 + c) * Lambda) := by gcongr
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem sk_size_factor {q Lambda nu : ℝ} {N : ℕ}
    (hq : 0 < q) (hq1 : q < 1) (hLam : 0 ≤ Lambda) (hnu : 0 ≤ nu)
    (hsmall : Lambda ≤ nu * N) :
    (N : ℝ) + edgeCutoff q Lambda + 1 ≤
      (2 + nu / Real.log (1/q)) * ((N : ℝ) + 1) := by
  have hd := log_inv_pos hq hq1
  have hL := edgeCutoff_le hq hq1 hLam
  have hl := div_le_div_of_nonneg_right hsmall hd.le
  have heq : nu * (N : ℝ) / Real.log (1/q) = (nu / Real.log (1/q)) * N := by ring
  rw [heq] at hl
  have hn : 0 ≤ nu / Real.log (1/q) := div_nonneg hnu hd.le
  nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

end SpinGlass.PolynomialRuntime
