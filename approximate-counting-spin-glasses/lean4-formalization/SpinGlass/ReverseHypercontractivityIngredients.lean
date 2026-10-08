import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Scalar ingredients for an elementary reverse-hypercontractive proof

This file proves the complete scalar power inequality needed to compare the
curvatures of a two-point power mean and a geometrically averaged noisy pair.
It does not prove the derivative identities, the resulting analytic two-point
inequality, or its tensorization to the cube within this file. Those arguments
are proved in the accompanying TwoPoint, Tensorization, and ReverseHypercontractivity modules.
-/

noncomputable section
open Real Set
namespace SpinGlass.ReverseHypercontractivityIngredients

lemma power_average_pos {r x : ℝ} (hx : 0 < x) : 0 < (x ^ r + 1) / 2 := by
  have := Real.rpow_pos_of_pos hx r
  positivity

lemma geometric_le_power_average {r x : ℝ} (hx : 0 < x) :
    x ^ (r / 2) ≤ (x ^ r + 1) / 2 := by
  have hs : (x ^ (r / 2)) ^ 2 = x ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  nlinarith [sq_nonneg (x ^ (r / 2) - 1)]

lemma power_average_le_arithmetic_power {r x : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hx : 0 < x) : (x ^ r + 1) / 2 ≤ ((x + 1) / 2) ^ r := by
  have hi : 1 ≤ 1 / r := (le_div_iff₀ hr).2 (by simpa)
  have h := (convexOn_rpow hi).2 (show 0 ≤ x ^ r from (rpow_pos_of_pos hx r).le)
    (show 0 ≤ (1 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, Real.one_rpow, mul_one] at h
  have heq : (x ^ r) ^ (1 / r) = x := by
    rw [← Real.rpow_mul hx.le, mul_one_div_cancel hr.ne', Real.rpow_one]
  rw [heq] at h
  have h' := Real.rpow_le_rpow (by positivity : 0 ≤ ((1 / 2 : ℝ) * x ^ r + 1 / 2) ^ (1 / r)) h hr.le
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr.ne', Real.rpow_one] at h'
  convert h' using 1 <;> congr 1 <;> ring

/-- The positive factor in minus the second derivative of the two-point r-mean
is at least x^(-3/2) when r≤1/2. This is an actual scalar power inequality. -/
lemma curvature_factor_lower_small {r x : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    (hx : 0 < x) :
    x ^ (-3 / 2 : ℝ) ≤ ((x ^ r + 1) / 2) ^ (1 / r - 2) * x ^ (r - 2) := by
  have he : 0 ≤ 1 / r - 2 := by
    have : 2 ≤ 1 / r := (le_div_iff₀ hr).2 (by linarith)
    linarith
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _)
    (geometric_le_power_average hx (r := r)) he
  have h' := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx.le (r - 2))
  rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx] at h'
  have hexp : r / 2 * (1 / r - 2) + (r - 2) = -3 / 2 := by
    field_simp
    ring
  rwa [hexp] at h'

/-- Above r=1/2, the same curvature factor is at least the arithmetic mean cubed,
inverted. This is the second branch of the elementary curvature argument. -/
lemma curvature_factor_lower_large {r x : ℝ} (hr2 : 1 / 2 ≤ r) (hr1 : r ≤ 1)
    (hx : 0 < x) :
    ((x + 1) / 2) ^ (-3 : ℝ) ≤
      ((x ^ r + 1) / 2) ^ (1 / r - 2) * x ^ (r - 2) := by
  have hr : 0 < r := by linarith
  have hm : 0 < (x + 1) / 2 := by linarith
  have he : 1 / r - 2 ≤ 0 := by
    have : 1 / r ≤ 2 := (div_le_iff₀ hr).2 (by linarith)
    linarith
  have hB := Real.rpow_le_rpow_of_nonpos (power_average_pos hx)
    (power_average_le_arithmetic_power hr hr1 hx) he
  have hxmean : x ≤ ((x + 1) / 2) ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hxpow := Real.rpow_le_rpow_of_nonpos hx hxmean (show r - 2 ≤ 0 by linarith)
  have h := mul_le_mul hB hxpow (Real.rpow_nonneg (sq_nonneg _) _) (Real.rpow_nonneg (le_of_lt (power_average_pos hx)) _)
  rw [← Real.rpow_mul hm.le, ← Real.rpow_natCast, ← Real.rpow_mul hm.le, ← Real.rpow_add hm] at h
  have hexp : r * (1 / r - 2) + (2 : ℝ) * (r - 2) = -3 := by
    field_simp
    ring
  norm_num only [Nat.cast_ofNat] at h
  rwa [hexp] at h

lemma three_quarters_negative_power_bound : (3 / 4 : ℝ) ^ (-3 / 2 : ℝ) ≤ 2 := by
  have hs : ((3 / 4 : ℝ) ^ (-3 / 2 : ℝ)) ^ 2 = 64 / 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    norm_num
  nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (-3 / 2)]

/-- The product of the two outputs of one-coordinate noise applied to `(x,1)`. -/
def noisyProduct (θ x : ℝ) : ℝ :=
  (((1 + θ) * x + (1 - θ)) / 2) * (((1 - θ) * x + (1 + θ)) / 2)

lemma noisyProduct_ge_input {θ x : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ≤ noisyProduct θ x := by
  have hθsq : 0 ≤ 1 - θ ^ 2 := by nlinarith
  have h := mul_nonneg hθsq (sq_nonneg (x - 1))
  dsimp [noisyProduct]
  nlinarith

lemma noisyProduct_ge_arithmetic {θ x : ℝ} (hx : 0 ≤ x) :
    (1 - θ ^ 2) * ((x + 1) / 2) ^ 2 ≤ noisyProduct θ x := by
  have h := mul_nonneg (sq_nonneg θ) hx
  dsimp [noisyProduct]
  nlinarith

/-- This explicitly stated power inequality is the curvature comparison needed
for the elementary two-point reverse-hypercontractive argument. It does not
assert the analytic inequality: identifying these expressions as derivatives
and applying a convexity criterion remain separate proof obligations. -/
theorem curvature_comparison {r θ x : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hθr : θ ≤ 1 - r) (hx : 0 < x) :
    θ ^ 2 * noisyProduct θ x ^ (-3 / 2 : ℝ) ≤
      (1 - r) * ((x ^ r + 1) / 2) ^ (1 / r - 2) * x ^ (r - 2) := by
  have hθ1 : θ ≤ 1 := by linarith
  have hQ : x ≤ noisyProduct θ x := noisyProduct_ge_input hθ hθ1
  have hQpos : 0 < noisyProduct θ x := hx.trans_le hQ
  have hfactor : 0 ≤ ((x ^ r + 1) / 2) ^ (1 / r - 2) :=
    Real.rpow_nonneg (power_average_pos hx).le _
  by_cases hr2 : r ≤ 1 / 2
  · have hpow := Real.rpow_le_rpow_of_nonpos hx hQ (by norm_num : (-3 / 2 : ℝ) ≤ 0)
    have hθsq : θ ^ 2 ≤ 1 - r := by nlinarith
    calc
      θ ^ 2 * noisyProduct θ x ^ (-3 / 2 : ℝ)
          ≤ (1 - r) * x ^ (-3 / 2 : ℝ) :=
        mul_le_mul hθsq hpow (Real.rpow_nonneg hQpos.le _) (by linarith)
      _ ≤ (1 - r) * (((x ^ r + 1) / 2) ^ (1 / r - 2) * x ^ (r - 2)) :=
        mul_le_mul_of_nonneg_left (curvature_factor_lower_small hr hr2 hx) (by linarith)
      _ = _ := by ring
  · have hrlarge : 1 / 2 ≤ r := by linarith
    have hθhalf : θ ≤ 1 / 2 := by linarith
    have hm : 0 < (x + 1) / 2 := by linarith
    have hQlower : (3 / 4 : ℝ) * ((x + 1) / 2) ^ 2 ≤ noisyProduct θ x := by
      have hquad : 3 / 4 ≤ 1 - θ ^ 2 := by nlinarith
      exact (mul_le_mul_of_nonneg_right hquad (sq_nonneg _)).trans (noisyProduct_ge_arithmetic hx.le)
    have hpow := Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < (3 / 4 : ℝ) * ((x + 1) / 2) ^ 2) hQlower
      (by norm_num : (-3 / 2 : ℝ) ≤ 0)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 4) (sq_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul hm.le] at hpow
    norm_num only [Nat.cast_ofNat] at hpow
    have hpow' : noisyProduct θ x ^ (-3 / 2 : ℝ) ≤ 2 * ((x + 1) / 2) ^ (-3 : ℝ) := by
      have hc : (3 / 4 : ℝ) ^ (-(3 / 2) : ℝ) ≤ 2 := by
        convert three_quarters_negative_power_bound using 1
        congr 1
        ring
      have hfinal := hpow.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hm.le (-3)))
      convert hfinal using 1 <;> congr 2 <;> ring
    have hθsq : 2 * θ ^ 2 ≤ 1 - r := by nlinarith
    calc
      θ ^ 2 * noisyProduct θ x ^ (-3 / 2 : ℝ)
          ≤ θ ^ 2 * (2 * ((x + 1) / 2) ^ (-3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow' (sq_nonneg θ)
      _ = (2 * θ ^ 2) * ((x + 1) / 2) ^ (-3 : ℝ) := by ring
      _ ≤ (1 - r) * ((x + 1) / 2) ^ (-3 : ℝ) :=
        mul_le_mul_of_nonneg_right hθsq (Real.rpow_nonneg hm.le _)
      _ ≤ (1 - r) * (((x ^ r + 1) / 2) ^ (1 / r - 2) * x ^ (r - 2)) :=
        mul_le_mul_of_nonneg_left (curvature_factor_lower_large hrlarge hr1.le hx) (by linarith)
      _ = _ := by ring

end SpinGlass.ReverseHypercontractivityIngredients
