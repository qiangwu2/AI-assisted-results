import SpinGlass.UniformMassEntropy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Positivity of the full graphical threshold and its exact SK normalization. -/

noncomputable section
namespace SpinGlass.Threshold
open Real
open SpinGlass.UniformMassEntropy

/-- The elementary weighted logarithm inequality underlying the entropy duality. -/
theorem weighted_log_le {y b : ℝ} (hy : 0 < y) (hb : 0 < b) :
    y*(Real.log b - Real.log y) ≤ b-y := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb hy)) hy.le
  rw [Real.log_div hb.ne' hy.ne'] at h
  have heq : y*(b/y-1) = b-y := by field_simp
  rwa [heq] at h

/-- Exact entropy is the convex dual upper bound of every sign-cube tilt. -/
theorem entropy_ge_tilt {x : ℝ} (hx : -1 < x) (hx1 : x < 1) (t : ℝ) :
    t*x - Real.log (Real.cosh t) ≤ entropy x := by
  have hp : 0 < 1+x := by linarith
  have hm : 0 < 1-x := by linarith
  have hc := Real.cosh_pos t
  have hplus := weighted_log_le hp (div_pos (Real.exp_pos t) hc)
  have hminus := weighted_log_le hm (div_pos (Real.exp_pos (-t)) hc)
  rw [Real.log_div (Real.exp_pos t).ne' hc.ne', Real.log_exp] at hplus
  rw [Real.log_div (Real.exp_pos (-t)).ne' hc.ne', Real.log_exp] at hminus
  have hnorm : Real.exp t / Real.cosh t + Real.exp (-t) / Real.cosh t = 2 := by
    have htwo : Real.exp t + Real.exp (-t) = 2*Real.cosh t := by rw [Real.cosh_eq]; ring
    rw [← add_div, htwo]
    field_simp
  unfold entropy
  nlinarith

/-- The exact entropy dominates its quadratic term, including the endpoint. -/
theorem entropy_ge_half_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x^2/2 ≤ entropy x := by
  obtain hxlt | rfl := hx1.lt_or_eq
  · have ht := entropy_ge_tilt (by linarith) hxlt x
    have hc := Real.log_le_log (Real.cosh_pos x) (Real.cosh_le_exp_half_sq x)
    rw [Real.log_exp] at hc
    nlinarith
  · rw [entropy_one]
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h

/-- A matching upper estimate near zero, proved with elementary logarithm bounds. -/
theorem entropy_le_half_sq_mul_one_add {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    entropy x ≤ x^2*(1+x)/2 := by
  have hp : 0 < 1+x := by linarith
  have hm : 0 < 1-x := by linarith
  have hpq : 0 < 1-x^2 := by nlinarith
  have hplus := Real.log_le_sub_one_of_pos hp
  have hprod := Real.log_le_sub_one_of_pos hpq
  have heq : Real.log (1-x^2) = Real.log (1+x)+Real.log (1-x) := by
    rw [← Real.log_mul hp.ne' hm.ne']
    congr 1
    ring
  have h1 := mul_le_mul_of_nonneg_left hplus hx
  have h2 := mul_le_mul_of_nonneg_left hprod hm.le
  rw [heq] at h2
  unfold entropy
  nlinarith

/-- For every interaction order at least two, the full threshold is bounded
below by `p!/2`, so the permitted high-temperature range is nonempty. -/
theorem factorial_half_le_threshold {p : ℕ} (hp : 2 ≤ p) :
    (p.factorial : ℝ)/2 ≤ thresholdSquared p := by
  apply le_csInf (threshold_set_nonempty p)
  rintro y ⟨x, hx, rfl⟩
  have hxpow : 0 < x^p := pow_pos hx.1 p
  have hpow : x^p ≤ x^2 := pow_le_pow_of_le_one hx.1.le hx.2 hp
  have hI := entropy_ge_half_sq hx.1.le hx.2
  apply (le_div_iff₀ hxpow).mpr
  have hf : (0:ℝ) ≤ p.factorial := Nat.cast_nonneg _
  nlinarith

theorem thresholdSquared_pos {p : ℕ} (hp : 2 ≤ p) : 0 < thresholdSquared p := by
  exact lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (by norm_num))
    (factorial_half_le_threshold hp)

/-- The manuscript's SK threshold is exactly one in the unordered-edge convention. -/
theorem thresholdSquared_two : thresholdSquared 2 = 1 := by
  have hlo : (1:ℝ) ≤ thresholdSquared 2 := by
    simpa using factorial_half_le_threshold (p := 2) (by norm_num)
  apply le_antisymm _ hlo
  by_contra h
  have hT : 1 < thresholdSquared 2 := lt_of_not_ge h
  let x := min ((thresholdSquared 2 - 1)/2) (1/2 : ℝ)
  have hx : 0 < x := lt_min (by linarith) (by norm_num)
  have hx1 : x < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hxt : x < thresholdSquared 2 - 1 := by
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hinf := thresholdSquared_le 2 hx hx1.le
  have hupper := entropy_le_half_sq_mul_one_add hx.le hx1
  have hratio : (2:ℝ)*entropy x/x^2 ≤ 1+x := by
    apply (div_le_iff₀ (sq_pos_of_pos hx)).mpr
    nlinarith
  norm_num at hinf
  linarith

end SpinGlass.Threshold
