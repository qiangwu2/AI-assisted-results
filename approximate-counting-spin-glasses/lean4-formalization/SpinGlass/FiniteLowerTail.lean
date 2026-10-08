import SpinGlass.ReverseHypercontractivity
import SpinGlass.LowerTail

/-!
# The unconditional finite-cube lower-tail estimate

For a strictly positive function of uniform independent signs with mean one,
the proved reverse-hypercontractive theorem and moment interpolation bound the
specified negative moment of its noise transform by its second moment. A finite
Markov argument gives the corresponding actual proportion of cube points.

This file does not integrate over random coupling magnitudes or prove the
spin-glass coefficient-mass bound.
-/

noncomputable section

namespace SpinGlass.FiniteLowerTail

open Finset Real
open SpinGlass.Expansion SpinGlass.Noise SpinGlass.LowerTail
open SpinGlass.ReverseHypercontractivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise order implies order of uniform finite-cube expectations. -/
theorem spinMean_mono (f g : (ι → Bool) → ℝ) (hfg : ∀ ε, f ε ≤ g ε) :
    spinMean f ≤ spinMean g := by
  unfold spinMean
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ε hε => hfg ε))
  exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)

/-- The previously proved finite weighted interpolation specializes to uniform signs. -/
theorem spinMean_interpolation (f : (ι → Bool) → ℝ) (hf : ∀ ε, 0 < f ε)
    (hmean : spinMean f = 1) {r : ℝ} (hr : r < 1) :
    (spinMean (fun ε => f ε ^ r)) ^ (-1 / (1 - r)) ≤
      spinMean (fun ε => f ε ^ 2) := by
  have hmean' : (∑ ε : ι → Bool, (∏ _i : ι, (1 / 2 : ℝ)) * f ε) = 1 := by
    rw [uniform_weighted_sum]
    exact hmean
  have h := interpolation_negative_power_bound Finset.univ
    (fun _ : ι → Bool => ∏ _i : ι, (1 / 2 : ℝ)) f
    (fun ε hε => Finset.prod_nonneg (fun i hi => by norm_num))
    (fun ε hε => hf ε) hmean' hr
  simpa only [uniform_weighted_sum] using h

/-- The finite-cube negative moment used in the manuscript, with the actual
reverse-hypercontractive theorem discharged and the prescribed exponent. -/
theorem noisy_negative_moment_le_second_moment {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (f : (ι → Bool) → ℝ) (hf : ∀ ε, 0 < f ε) (hmean : spinMean f = 1) :
    spinMean (fun ε => (cubeNoise θ f ε) ^ (-((1 - Real.sqrt θ) / Real.sqrt θ))) ≤
      spinMean (fun ε => f ε ^ 2) := by
  have hr := fractionalExponent_pos hθ hθ1
  have hr1 := fractionalExponent_lt_one hθ
  have hs := negativeExponent_pos hθ hθ1
  have hparam : θ ≤ (1 - (1 - Real.sqrt θ)) /
      (1 + (1 - Real.sqrt θ) / Real.sqrt θ) := (noiseParameter_identity hθ).ge
  have hRH := negative_moment hr hr1 hs hθ hparam f hf
  have hI := spinMean_interpolation f hf hmean hr1
  have heq : -((1 - Real.sqrt θ) / Real.sqrt θ) / (1 - Real.sqrt θ) =
      -1 / (1 - (1 - Real.sqrt θ)) := by
    have hroot : Real.sqrt θ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hθ)
    have hfrac : 1 - Real.sqrt θ ≠ 0 := ne_of_gt hr
    have hone : 1 - (1 - Real.sqrt θ) = Real.sqrt θ := by ring
    rw [hone]
    field_simp
  rw [heq] at hRH
  exact hRH.trans hI

/-- A lower-tail indicator is bounded pointwise by the scaled negative moment. -/
theorem lower_tail_indicator_le {x z s : ℝ} (hx : 0 < x) (hz : 0 < z) (hs : 0 < s) :
    (if x < z then (1 : ℝ) else 0) ≤ z ^ s * x ^ (-s) := by
  split_ifs with hxz
  · have hp : z ^ (-s) ≤ x ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hx hxz.le (by linarith)
    calc
      1 = z ^ s * z ^ (-s) := by rw [← Real.rpow_add hz]; simp
      _ ≤ z ^ s * x ^ (-s) := mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hz s).le
  · exact mul_nonneg (Real.rpow_pos_of_pos hz s).le (Real.rpow_pos_of_pos hx (-s)).le

/-- Finite Markov inequality, stated as the actual proportion of cube points
where a positive function is less than `z`. -/
theorem finite_markov_lower_tail (h : (ι → Bool) → ℝ) (hh : ∀ ε, 0 < h ε)
    {s z : ℝ} (hs : 0 < s) (hz : 0 < z) :
    ((Finset.univ.filter (fun ε : ι → Bool => h ε < z)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card ι ≤
      spinMean (fun ε => h ε ^ (-s)) * z ^ s := by
  have hm := spinMean_mono (fun ε => if h ε < z then (1 : ℝ) else 0)
    (fun ε => z ^ s * h ε ^ (-s)) (fun ε => lower_tail_indicator_le (hh ε) hz hs)
  rw [spinMean_mul_left] at hm
  have hindicator : spinMean (fun ε => if h ε < z then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun ε : ι → Bool => h ε < z)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card ι := by
    unfold spinMean
    rw [Finset.sum_boole]
    ring
  rw [hindicator] at hm
  simpa only [mul_comm] using hm

/-- The finite-cube lower-tail probability is bounded by `E[f²] * z^s`, with
the paper's `s = (1 - √θ) / √θ`. No lower-tail estimate is assumed. -/
theorem noisy_lower_tail_le_second_moment {θ z : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z)
    (f : (ι → Bool) → ℝ) (hf : ∀ ε, 0 < f ε) (hmean : spinMean f = 1) :
    ((Finset.univ.filter (fun ε : ι → Bool => cubeNoise θ f ε < z)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card ι ≤
      spinMean (fun ε => f ε ^ 2) * z ^ ((1 - Real.sqrt θ) / Real.sqrt θ) := by
  have hnoise : ∀ ε, 0 < cubeNoise θ f ε := by
    intro ε
    exact cubeNoise_pos (by linarith) hθ1 f hf ε
  have hmarkov := finite_markov_lower_tail (cubeNoise θ f) hnoise
    (negativeExponent_pos hθ hθ1) hz
  exact hmarkov.trans (mul_le_mul_of_nonneg_right
    (noisy_negative_moment_le_second_moment hθ hθ1 f hf hmean)
    (Real.rpow_pos_of_pos hz _).le)

end SpinGlass.FiniteLowerTail
