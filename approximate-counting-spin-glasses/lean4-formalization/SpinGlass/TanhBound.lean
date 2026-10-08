import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The scalar contraction used to bound the disorder second moment. -/

namespace SpinGlass.TanhBound

theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have hd : ∀ t : ℝ, HasDerivAt
      (fun y : ℝ => y * Real.cosh y - Real.sinh y) (t * Real.sinh t) t := by
    intro t
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
      (Real.hasDerivAt_sinh t) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hn : ∀ t : ℝ, 0 ≤ t * Real.sinh t := by
    intro t
    rcases le_total 0 t with ht | ht
    · exact mul_nonneg ht (Real.sinh_nonneg_iff.mpr ht)
    · exact mul_nonneg_of_nonpos_of_nonpos ht (Real.sinh_nonpos_iff.mpr ht)
  have hmono := monotone_of_hasDerivAt_nonneg hd hn
  have h := hmono hx
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h
  linarith

theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact (div_le_iff₀ (Real.cosh_pos x)).2 (sinh_le_mul_cosh hx)

theorem abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  have hp : |Real.tanh x| = Real.tanh |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, abs_of_nonneg]
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le
    · have hs : Real.tanh x ≤ 0 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hx) (Real.cosh_pos x).le
      rw [abs_of_nonpos hx, Real.tanh_neg, abs_of_nonpos hs]
  rw [hp]
  exact tanh_le_self (abs_nonneg x)

theorem tanh_sq_le_sq (x : ℝ) : Real.tanh x ^ 2 ≤ x ^ 2 := by
  have h := abs_tanh_le_abs x
  nlinarith [sq_abs (Real.tanh x), sq_abs x, abs_nonneg (Real.tanh x), abs_nonneg x]

end SpinGlass.TanhBound
