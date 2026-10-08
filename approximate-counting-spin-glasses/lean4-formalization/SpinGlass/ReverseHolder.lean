import SpinGlass.LowerTail

/-!
# Finite weighted duality for a negative moment

The main reduction in this file assumes a bilinear lower bound for every positive
test function. It proves the negative-moment consequence by an explicit test
function. This is a duality lemma, not a proof of reverse hypercontractivity or
of the assumed bilinear bound for a noise operator.
-/

namespace SpinGlass.ReverseHolder

open Finset Real

/-- A strictly positive function has strictly positive real moments under finite
probability weights, even when some weights vanish. -/
theorem weighted_rpow_sum_pos {ι : Type*} (S : Finset ι) (w h : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hw1 : ∑ i ∈ S, w i = 1)
    (hh : ∀ i ∈ S, 0 < h i) (p : ℝ) :
    0 < ∑ i ∈ S, w i * h i ^ p := by
  have hsome : ∃ i ∈ S, 0 < w i := by
    apply (Finset.sum_pos_iff_of_nonneg hw).1
    rw [hw1]
    norm_num
  obtain ⟨i, hi, hwi⟩ := hsome
  apply (Finset.sum_pos_iff_of_nonneg
    (fun j hj => mul_nonneg (hw j hj) (Real.rpow_pos_of_pos (hh j hj) p).le)).2
  exact ⟨i, hi, mul_pos hwi (Real.rpow_pos_of_pos (hh i hi) p)⟩

/-- The positive exponent dual to the negative exponent `-s`. -/
theorem dualExponent_pos {s : ℝ} (hs : 0 < s) : 0 < s / (1 + s) := by
  exact div_pos hs (by linarith)

theorem dualExponent_lt_one {s : ℝ} (hs : 0 < s) : s / (1 + s) < 1 := by
  apply (div_lt_one (by linarith : 0 < 1 + s)).2
  linarith

theorem dualExponent_power_identity {s : ℝ} (hs : 0 < s) :
    (-s - 1) * (s / (1 + s)) = -s := by
  have hne : 1 + s ≠ 0 := by linarith
  field_simp
  ring

theorem dualExponent_inverse_identity {s : ℝ} (hs : 0 < s) :
    1 - 1 / (s / (1 + s)) = (-s)⁻¹ := by
  have hne : s ≠ 0 := hs.ne'
  have hne1 : 1 + s ≠ 0 := by linarith
  field_simp
  ring

/-- A scalar rearrangement used by the finite duality argument. -/
theorem negative_moment_of_power_bound {A K s : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hs : 0 < s)
    (hbound : K * A ^ (1 / (s / (1 + s))) ≤ A) :
    A ≤ K ^ (-s) := by
  have hquot : K ≤ A / A ^ (1 / (s / (1 + s))) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hA _)).2 hbound
  have heq : A / A ^ (1 / (s / (1 + s))) = A ^ ((-s)⁻¹) := by
    rw [← dualExponent_inverse_identity hs, Real.rpow_sub hA, Real.rpow_one]
  rw [heq] at hquot
  exact (Real.le_rpow_inv_iff_of_neg hK hA (neg_neg_of_pos hs)).1 hquot

/-- A bilinear lower bound valid for every positive test function implies the
negative-moment bound. The proof uses the actual finite test function
`g i = h i ^ (-s - 1)`; the bilinear estimate is an explicit hypothesis. -/
theorem negative_moment_of_bilinear {ι : Type*} (S : Finset ι) (w h : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hw1 : ∑ i ∈ S, w i = 1)
    (hh : ∀ i ∈ S, 0 < h i) {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hbilinear : ∀ g : ι → ℝ, (∀ i ∈ S, 0 < g i) →
      K * (∑ i ∈ S, w i * g i ^ (s / (1 + s))) ^ (1 / (s / (1 + s))) ≤
        ∑ i ∈ S, w i * h i * g i) :
    (∑ i ∈ S, w i * h i ^ (-s)) ≤ K ^ (-s) := by
  have hA := weighted_rpow_sum_pos S w h hw hw1 hh (-s)
  have htest := hbilinear (fun i => h i ^ (-s - 1))
    (fun i hi => Real.rpow_pos_of_pos (hh i hi) _)
  have htest_moment :
      (∑ i ∈ S, w i * (h i ^ (-s - 1)) ^ (s / (1 + s))) =
        ∑ i ∈ S, w i * h i ^ (-s) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hh i hi).le, dualExponent_power_identity hs]
  have htest_pairing :
      (∑ i ∈ S, w i * h i * h i ^ (-s - 1)) =
        ∑ i ∈ S, w i * h i ^ (-s) := by
    apply Finset.sum_congr rfl
    intro i hi
    have heq : h i ^ (-s) = h i ^ (-s - 1) * h i := by
      calc
        h i ^ (-s) = h i ^ ((-s - 1) + 1) := by congr 1; ring
        _ = h i ^ (-s - 1) * h i := Real.rpow_add_one (hh i hi).ne' (-s - 1)
    rw [heq]
    ring
  rw [htest_moment, htest_pairing] at htest
  exact negative_moment_of_power_bound hA hK hs htest

end SpinGlass.ReverseHolder
