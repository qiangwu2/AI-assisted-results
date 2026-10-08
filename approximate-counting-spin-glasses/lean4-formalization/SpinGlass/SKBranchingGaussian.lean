import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import SpinGlass.SKBranchingPairings
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Explicit auxiliary Gaussian moments for the SK branching count. -/
noncomputable section
namespace SpinGlass.SKBranching
open scoped BigOperators Nat
open MeasureTheory Real Set

/-- All even polynomial powers times a strictly decaying Gaussian are integrable. -/
theorem integrable_even_gaussian (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ (2 * k) * Real.exp (-b * x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb
    (show (-1 : ℝ) < (2 * k : ℕ) from lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  simpa only [Real.rpow_natCast] using h

/-- Exact half-line moment from the verified Gamma integral. -/
theorem integral_even_gaussian_Ioi (k : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x ^ (2 * k) * Real.exp (-b * x ^ 2)) =
      b ^ (-((k : ℝ) + 1 / 2)) * (1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (2 * k : ℕ))
    (by norm_num) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)) hb
  have he : (((2 * k : ℕ) : ℝ) + 1) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
  simpa only [Real.rpow_natCast, Real.rpow_two, neg_div, he] using h

/-- The full-line even moment, with no probabilistic Gaussian lemma assumed. -/
theorem integral_even_gaussian (k : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, x ^ (2 * k) * Real.exp (-b * x ^ 2)) =
      b ^ (-((k : ℝ) + 1 / 2)) * Real.Gamma ((k : ℝ) + 1 / 2) := by
  let f : ℝ → ℝ := fun x => x ^ (2 * k) * Real.exp (-b * x ^ 2)
  have hneg : (∫ x : ℝ in Iic 0, f x) = ∫ x : ℝ in Ioi 0, f x := by
    calc
      _ = ∫ x : ℝ in Ioi 0, f (-x) := by
        simpa using (integral_comp_neg_Ioi 0 f).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp [f, neg_pow, pow_mul]
  rw [← integral_add_compl measurableSet_Ioi (integrable_even_gaussian k hb), compl_Ioi]
  change (∫ x in Ioi 0, f x) + (∫ x in Iic 0, f x) = _
  rw [hneg]
  change (∫ x : ℝ in Ioi 0, x ^ (2 * k) * Real.exp (-b * x ^ 2)) + _ = _
  rw [integral_even_gaussian_Ioi k hb]
  ring

/-- Standard normal expectation as its explicit normalized Lebesgue integral. -/
def gaussianMean (f : ℝ → ℝ) : ℝ :=
  (2 : ℝ) ^ (-(1 / 2 : ℝ)) / Real.sqrt Real.pi *
    ∫ x : ℝ, f x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)

/-- Exact tilted even moment, including the empty moment k=0. -/
theorem gaussianMean_tilted_even_moment (k : ℕ) {t : ℝ} (ht : t < 1) :
    gaussianMean (fun x : ℝ => x ^ (2 * k) * Real.exp (t * x ^ 2 / 2)) =
      ((2 * k - 1)‼ : ℝ) * (1 - t) ^ (-((k : ℝ) + 1 / 2)) := by
  have hb : 0 < (1 - t) / 2 := by linarith
  have hcombine (x : ℝ) :
      (x ^ (2 * k) * Real.exp (t * x ^ 2 / 2)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
        x ^ (2 * k) * Real.exp (-((1 - t) / 2) * x ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  unfold gaussianMean
  simp_rw [hcombine]
  rw [integral_even_gaussian k hb, Real.Gamma_nat_add_half]
  rw [Real.div_rpow (by linarith : 0 ≤ 1 - t) (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (2 : ℝ) ^ (-(1 / 2 : ℝ)) /
      (2 : ℝ) ^ (-((k : ℝ) + 1 / 2)) = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub (by norm_num)]
    congr 1
    ring
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    _ = ((2 * k - 1)‼ : ℝ) * (1 - t) ^ (-((k : ℝ) + 1 / 2)) *
        (((2 : ℝ) ^ (-(1 / 2 : ℝ)) / (2 : ℝ) ^ (-((k : ℝ) + 1 / 2))) / (2 : ℝ) ^ k) := by
      field_simp [hpi]
    _ = _ := by rw [hpow, div_self (ne_of_gt (pow_pos (by norm_num) k)), mul_one]

/-- The auxiliary density is normalized. -/
theorem gaussianMean_one : gaussianMean (fun _ => 1) = 1 := by
  simpa [gaussianMean] using gaussianMean_tilted_even_moment 0 (t := 0) (by norm_num)

end SpinGlass.SKBranching
