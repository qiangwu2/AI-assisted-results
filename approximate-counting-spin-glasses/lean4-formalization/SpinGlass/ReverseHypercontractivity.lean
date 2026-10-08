import SpinGlass.BilinearTwoPoint
import SpinGlass.NoiseMomentReduction

/-!
# Finite Boolean-cube reverse hypercontractivity

This file discharges the scalar and bilinear premises of the component lemmas.
The result is unconditional under its stated positivity and parameter hypotheses;
there is no axiom or assumption asserting reverse hypercontractivity.
-/

namespace SpinGlass.ReverseHypercontractivity
open Finset Real
open SpinGlass.Expansion SpinGlass.Noise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Constant product weights give exactly uniform spin averaging. -/
theorem uniform_weighted_sum (f : (ι → Bool) → ℝ) :
    (∑ ε : ι → Bool, (∏ _i : ι, (1 / 2 : ℝ)) * f ε) = spinMean f := by
  simp only [Finset.prod_const, Finset.card_univ, ← Finset.mul_sum, spinMean,
    one_div, inv_pow]

/-- Reverse hypercontractivity in the negative-moment form used by the paper.
The bound is proved for every finite dimension and every strictly positive function. -/
theorem negative_moment {θ r s : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hs : 0 < s)
    (hθ : 0 < θ) (hθrs : θ ≤ (1 - r) / (1 + s))
    (f : (ι → Bool) → ℝ) (hf : ∀ ε, 0 < f ε) :
    spinMean (fun ε => (cubeNoise θ f ε) ^ (-s)) ≤
      (spinMean (fun ε => f ε ^ r)) ^ (-s / r) := by
  have hden : 0 < 1 + s := by linarith
  have ht : 0 < s / (1 + s) := div_pos hs hden
  have ht1 : s / (1 + s) < 1 := by
    apply (div_lt_iff₀ hden).2
    linarith
  have hprod : (1 - r) * (1 - s / (1 + s)) = (1 - r) / (1 + s) := by
    field_simp
    ring
  have hθ1 : θ < 1 := by
    have hfrac : (1 - r) / (1 + s) < 1 := by
      apply (div_lt_iff₀ hden).2
      linarith
    exact lt_of_le_of_lt hθrs hfrac
  have hbit := BilinearTwoPoint.bit_reverse_bound hr hr1 ht ht1 hθ.le
    (by simpa only [hprod] using hθrs)
  have hcube := Tensorization.bool_cube_reverse_bound_fintype (ι := ι)
    (by linarith : -1 ≤ θ) hθ1.le (ne_of_gt hr) (ne_of_gt ht) hbit
  have hnegative := NoiseMomentReduction.negative_moment_of_cube_bilinear θ r s
    hθ.le hθ1 hs f hf (by
      intro g hg
      have h := hcube f g hf hg
      simpa only [Tensorization.powerMean, Tensorization.bilinear,
        Tensorization.bitJoint, Finset.prod_const, Finset.card_univ] using h)
  simpa only [uniform_weighted_sum] using hnegative


/-- A strictly positive function has a strictly positive uniform average. -/
theorem spinMean_pos (f : (ι → Bool) → ℝ) (hf : ∀ ε, 0 < f ε) :
    0 < spinMean f := by
  unfold spinMean
  apply mul_pos (inv_pos.mpr (pow_pos (by norm_num) _))
  exact Finset.sum_pos (fun ε _ => hf ε) Finset.univ_nonempty

/-- The exact reverse-norm formulation of the paper's reverse-hypercontractivity lemma. -/
theorem reverse_norm {θ r t : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : t < 0)
    (hθ : 0 < θ) (hθrt : θ ≤ (1 - r) / (1 - t))
    (f : (ι → Bool) → ℝ) (hf : ∀ ε, 0 < f ε) :
    (spinMean (fun ε => f ε ^ r)) ^ (1 / r) ≤
      (spinMean (fun ε => (cubeNoise θ f ε) ^ t)) ^ (1 / t) := by
  have hs : 0 < -t := by linarith
  have hθ1 : θ < 1 := by
    have hden : 0 < 1 - t := by linarith
    have hfrac : (1 - r) / (1 - t) < 1 := by
      apply (div_lt_iff₀ hden).2
      linarith
    exact lt_of_le_of_lt hθrt hfrac
  have hbound := negative_moment hr hr1 hs hθ
    (by simpa only [sub_eq_add_neg] using hθrt) f hf
  simp only [neg_neg] at hbound
  have hA := spinMean_pos (fun ε => cubeNoise θ f ε ^ t) (by
    intro ε
    exact Real.rpow_pos_of_pos (cubeNoise_pos (by linarith) hθ1 f hf ε) t)
  have hB := spinMean_pos (fun ε => f ε ^ r) (fun ε => Real.rpow_pos_of_pos (hf ε) r)
  have hexponent : 1 / t ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) ht.le
  have hpower := Real.rpow_le_rpow_of_nonpos hA hbound hexponent
  rw [← Real.rpow_mul hB.le] at hpower
  have heq : (t / r) * (1 / t) = 1 / r := by
    field_simp [ne_of_lt ht]
  rwa [heq] at hpower

end SpinGlass.ReverseHypercontractivity

