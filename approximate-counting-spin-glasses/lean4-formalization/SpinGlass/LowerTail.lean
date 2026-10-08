import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Proven analytic ingredients for the lower-tail argument

This file proves finite weighted moment interpolation and the manuscript's
choice of exponents. The independent finite-cube reverse-hypercontractivity
proof is in `SpinGlass.ReverseHypercontractivity`.
-/

namespace SpinGlass.LowerTail

open Finset Real Set

/-- Negative powers are convex on the strictly positive half-line. -/
theorem convexOn_rpow_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ p) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : 0 < a * x + b * y := by
    exact (convex_Ioi (0 : ℝ)) hx hy ha hb hab
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hlog ⊢
  rw [Real.rpow_def_of_pos hxy, Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos hy]
  calc
    Real.exp (Real.log (a * x + b * y) * p)
        ≤ Real.exp ((a * Real.log x + b * Real.log y) * p) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlog hp)
    _ = Real.exp (a * (Real.log x * p) + b * (Real.log y * p)) := by congr 1; ring
    _ ≤ a * Real.exp (Real.log x * p) + b * Real.exp (Real.log y * p) :=
      convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab

/-- If `∑ wᵢ fᵢ = 1`, size-biasing by `f` and applying Jensen gives the
second-moment interpolation bound used in the manuscript. In particular, for
probability weights and `0 < r < 1`, this is `E f^r ≥ (E f²)^{-(1-r)}`. -/
theorem moment_interpolation {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hf : ∀ i ∈ S, 0 < f i)
    (hmean : ∑ i ∈ S, w i * f i = 1) {r : ℝ} (hr : r ≤ 1) :
    (∑ i ∈ S, w i * f i ^ 2) ^ (r - 1) ≤ ∑ i ∈ S, w i * f i ^ r := by
  have hJ := (convexOn_rpow_nonpos (p := r - 1) (by linarith)).map_sum_le
    (t := S) (w := fun i => w i * f i) (p := f)
    (fun i hi => mul_nonneg (hw i hi) (hf i hi).le) hmean hf
  simp only [smul_eq_mul] at hJ
  have hleft : (∑ i ∈ S, w i * f i * f i) = ∑ i ∈ S, w i * f i ^ 2 := by
    apply sum_congr rfl
    intro i hi
    ring
  have hright : (∑ i ∈ S, w i * f i * f i ^ (r - 1)) =
      ∑ i ∈ S, w i * f i ^ r := by
    apply sum_congr rfl
    intro i hi
    rw [Real.rpow_sub (hf i hi), Real.rpow_one]
    field_simp [ne_of_gt (hf i hi)]
  rwa [hleft, hright] at hJ

/-- Every real moment is positive when the positive function has weighted mean one. -/
theorem weighted_moment_pos {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hf : ∀ i ∈ S, 0 < f i)
    (hmean : ∑ i ∈ S, w i * f i = 1) (p : ℝ) :
    0 < ∑ i ∈ S, w i * f i ^ p := by
  have hsome : ∃ i ∈ S, 0 < w i * f i := by
    apply (Finset.sum_pos_iff_of_nonneg
      (fun i hi => mul_nonneg (hw i hi) (hf i hi).le)).1
    rw [hmean]
    norm_num
  obtain ⟨i, hi, hif⟩ := hsome
  have hwi : 0 < w i := by
    by_contra h
    have hzero : w i = 0 := le_antisymm (le_of_not_gt h) (hw i hi)
    simp [hzero] at hif
  apply (Finset.sum_pos_iff_of_nonneg
    (fun j hj => mul_nonneg (hw j hj) (Real.rpow_pos_of_pos (hf j hj) p).le)).2
  exact ⟨i, hi, mul_pos hwi (Real.rpow_pos_of_pos (hf i hi) p)⟩

/-- Raising the interpolation bound to the needed negative power gives at most
the second moment. This theorem concerns `f` itself and uses no noise estimate. -/
theorem interpolation_negative_power_bound {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hf : ∀ i ∈ S, 0 < f i)
    (hmean : ∑ i ∈ S, w i * f i = 1) {r : ℝ} (hr : r < 1) :
    (∑ i ∈ S, w i * f i ^ r) ^ (-1 / (1 - r)) ≤ ∑ i ∈ S, w i * f i ^ 2 := by
  have hC : 0 < ∑ i ∈ S, w i * f i ^ 2 := by
    simpa using weighted_moment_pos S w f hw hf hmean 2
  have hbase := Real.rpow_pos_of_pos hC (r - 1)
  have hJ := moment_interpolation S w f hw hf hmean hr.le
  have hneg : -1 / (1 - r) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  have hpower := Real.rpow_le_rpow_of_nonpos hbase hJ hneg
  have heq : (r - 1) * (-1 / (1 - r)) = 1 := by
    have hne : 1 - r ≠ 0 := by linarith
    field_simp
    ring
  rw [← Real.rpow_mul hC.le, heq, Real.rpow_one] at hpower
  exact hpower

/-- Positivity of the fractional exponent `r = 1 - √θ`. -/
theorem fractionalExponent_pos {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 < 1 - Real.sqrt θ := by
  have hs : Real.sqrt θ < 1 := by
    simpa using Real.sqrt_lt_sqrt hθ.le hθ1
  linarith

/-- The selected fractional exponent lies below one. -/
theorem fractionalExponent_lt_one {θ : ℝ} (hθ : 0 < θ) :
    1 - Real.sqrt θ < 1 := by
  have hs := Real.sqrt_pos.2 hθ
  linarith

/-- The negative-moment exponent is strictly positive. -/
theorem negativeExponent_pos {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 < (1 - Real.sqrt θ) / Real.sqrt θ :=
  div_pos (fractionalExponent_pos hθ hθ1) (Real.sqrt_pos.2 hθ)

/-- The manuscript's two formulas for `s` agree. -/
theorem negativeExponent_eq {θ : ℝ} (hθ : 0 < θ) :
    (1 - Real.sqrt θ) / Real.sqrt θ = (Real.sqrt θ)⁻¹ - 1 := by
  have hs : Real.sqrt θ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hθ)
  field_simp

/-- The exponent also agrees with the real-power notation `θ^(-1/2)-1`. -/
theorem negativeExponent_rpow {θ : ℝ} (hθ : 0 < θ) :
    (1 - Real.sqrt θ) / Real.sqrt θ = θ ^ (-1 / 2 : ℝ) - 1 := by
  rw [negativeExponent_eq hθ, Real.sqrt_eq_rpow]
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hθ.le]

/-- Exact equality in the noise-parameter restriction of Corollary 1.11. -/
theorem noiseParameter_identity {θ : ℝ} (hθ : 0 < θ) :
    (1 - (1 - Real.sqrt θ)) /
      (1 + (1 - Real.sqrt θ) / Real.sqrt θ) = θ := by
  have hs : Real.sqrt θ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hθ)
  have hs2 := Real.sq_sqrt hθ.le
  field_simp
  nlinarith

/-- The final power of the second moment is exactly one. -/
theorem momentExponent_identity {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ((1 - Real.sqrt θ) / Real.sqrt θ) *
      (1 - (1 - Real.sqrt θ)) / (1 - Real.sqrt θ) = 1 := by
  have hs : Real.sqrt θ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hθ)
  have hr : 1 - Real.sqrt θ ≠ 0 := ne_of_gt (fractionalExponent_pos hθ hθ1)
  field_simp
  ring

end SpinGlass.LowerTail
