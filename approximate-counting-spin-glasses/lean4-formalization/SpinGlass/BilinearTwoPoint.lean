import SpinGlass.ReverseHypercontractivityTwoPoint
import SpinGlass.Tensorization

/-!
# The unconditional one-bit reverse bilinear inequality

The analytical input is the proved homogeneous two-point inequality.
The remaining argument is the reverse Cauchy inequality for two real coordinates.
-/

namespace SpinGlass.BilinearTwoPoint
open Real

/-- Reverse Cauchy inequality on the positive cone. -/
theorem reverse_cauchy {m n u v : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hu : |u| ≤ m) (hv : |v| ≤ n) :
    sqrt (m ^ 2 - u ^ 2) * sqrt (n ^ 2 - v ^ 2) ≤ m * n - u * v := by
  have hu2 : u ^ 2 ≤ m ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) hm).2 hu
  have hv2 : v ^ 2 ≤ n ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg v) hn).2 hv
  have hA : 0 ≤ m ^ 2 - u ^ 2 := sub_nonneg.mpr hu2
  have hB : 0 ≤ n ^ 2 - v ^ 2 := sub_nonneg.mpr hv2
  have huv : u * v ≤ m * n := by
    calc
      u * v ≤ |u * v| := le_abs_self _
      _ = |u| * |v| := abs_mul _ _
      _ ≤ m * n := mul_le_mul hu hv (abs_nonneg _) hm
  have hsq : (sqrt (m ^ 2 - u ^ 2) * sqrt (n ^ 2 - v ^ 2)) ^ 2 ≤
      (m * n - u * v) ^ 2 := by
    rw [mul_pow, sq_sqrt hA, sq_sqrt hB]
    nlinarith [sq_nonneg (m * v - n * u)]
  exact (sq_le_sq₀ (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
    (sub_nonneg.mpr huv)).mp hsq

/-- A contrast reduced by a factor in `[0,1]` is bounded by the positive mean. -/
theorem scaled_contrast_abs_le_mean {a b α : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    |α * ((a - b) / 2)| ≤ (a + b) / 2 := by
  rw [abs_mul, abs_of_nonneg hα]
  calc
    α * |(a - b) / 2| ≤ 1 * |(a - b) / 2| :=
      mul_le_mul_of_nonneg_right hα1 (abs_nonneg _)
    _ ≤ (a + b) / 2 := by
      rw [one_mul]
      exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Reducing the correlation below the product of contrast factors preserves the bound. -/
theorem contrast_bilinear_bound {m n d e α β θ : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hd : |α * d| ≤ m) (he : |β * e| ≤ n)
    (hab : 0 ≤ α * β) (hθ : 0 ≤ θ) (hθab : θ ≤ α * β) :
    sqrt (m ^ 2 - (α * d) ^ 2) * sqrt (n ^ 2 - (β * e) ^ 2) ≤
      m * n + θ * d * e := by
  by_cases hde : d * e ≤ 0
  · have hnneg : |-(β * e)| ≤ n := by simpa using he
    have h := reverse_cauchy hm hn hd hnneg
    have hmule := mul_le_mul_of_nonpos_right hθab hde
    simp only [neg_sq] at h
    nlinarith
  · have h := reverse_cauchy hm hn hd he
    have hdepos : 0 ≤ d * e := le_of_lt (lt_of_not_ge hde)
    have habde := mul_nonneg hab hdepos
    have hθde := mul_nonneg hθ hdepos
    nlinarith

/-- The scalar reverse bilinear inequality for arbitrary strictly positive inputs. -/
theorem scalar_bilinear {r t θ a b c d : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t) (ht1 : t < 1)
    (hθ : 0 ≤ θ) (hθrt : θ ≤ (1 - r) * (1 - t))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (((a ^ r + b ^ r) / 2) ^ (1 / r)) * (((c ^ t + d ^ t) / 2) ^ (1 / t)) ≤
      ((a + b) / 2) * ((c + d) / 2) + θ * ((a - b) / 2) * ((c - d) / 2) := by
  have hf := ReverseHypercontractivityTwoPoint.homogeneous_two_point_sq hr hr1 ha hb
  have hg := ReverseHypercontractivityTwoPoint.homogeneous_two_point_sq ht ht1 hc hd
  have hf' := Real.le_sqrt_of_sq_le hf
  have hg' := Real.le_sqrt_of_sq_le hg
  have hfp := ReverseHypercontractivityTwoPoint.two_point_powerMean_pos (r := r) ha hb
  have hgp := ReverseHypercontractivityTwoPoint.two_point_powerMean_pos (r := t) hc hd
  have hp := mul_le_mul hf' hg' hgp.le (sqrt_nonneg _)
  have hcontrast := contrast_bilinear_bound
    (by linarith : 0 ≤ (a + b) / 2) (by linarith : 0 ≤ (c + d) / 2)
    (scaled_contrast_abs_le_mean ha hb (by linarith : 0 ≤ 1 - r) (by linarith))
    (scaled_contrast_abs_le_mean hc hd (by linarith : 0 ≤ 1 - t) (by linarith))
    (mul_nonneg (by linarith : 0 ≤ 1 - r) (by linarith : 0 ≤ 1 - t)) hθ hθrt
  apply hp.trans
  simpa only [mul_div_assoc] using hcontrast

/-- The actual one-bit kernel satisfies the tensorization premise; it is not assumed. -/
theorem bit_reverse_bound {r t θ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t) (ht1 : t < 1)
    (hθ : 0 ≤ θ) (hθrt : θ ≤ (1 - r) * (1 - t)) :
    Tensorization.HasReverseBound (fun _ : Bool => (1 : ℝ) / 2)
      (fun _ : Bool => (1 : ℝ) / 2) (Tensorization.bitJoint θ) r t := by
  intro f g hf hg
  rw [Tensorization.powerMean_bool, Tensorization.powerMean_bool,
    Tensorization.bilinear_bitJoint]
  exact scalar_bilinear hr hr1 ht ht1 hθ hθrt (hf false) (hf true) (hg false) (hg true)

end SpinGlass.BilinearTwoPoint
