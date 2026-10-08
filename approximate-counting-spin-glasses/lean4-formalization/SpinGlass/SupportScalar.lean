import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Scalar factorial, binomial, and Poisson-tail bounds for the support estimates. -/

noncomputable section
namespace SpinGlass.SupportScalar
open Finset Real
open scoped BigOperators

theorem factorial_lower_bound (m : ℕ) :
    ((m : ℝ) / Real.exp 1) ^ m ≤ m.factorial := by
  have h := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
  have hf : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have he : 0 < Real.exp (m : ℝ) := Real.exp_pos _
  have hmul := (div_le_iff₀ hf).mp h
  have hexp : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    simpa using Real.exp_nat_mul 1 m
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (Real.exp_pos 1) _)).2
  rw [← hexp]
  simpa only [mul_comm] using hmul

theorem binomial_upper_bound (N k : ℕ) :
    (N.choose k : ℝ) ≤ (Real.exp 1 * N / k) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hden : 0 < ((k : ℝ) / Real.exp 1) ^ k :=
    pow_pos (div_pos hkpos (Real.exp_pos 1)) _
  calc
    (N.choose k : ℝ) ≤ (N : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k N
    _ ≤ (N : ℝ) ^ k / ((k : ℝ) / Real.exp 1) ^ k := by
      exact div_le_div_of_nonneg_left (by positivity) hden (factorial_lower_bound k)
    _ = (Real.exp 1 * N / k) ^ k := by
      rw [← div_pow]
      congr 1
      field_simp

theorem factorial_product_le (m j : ℕ) :
    (m.factorial : ℝ) * j.factorial ≤ (m + j).factorial := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (m + j))
    (Nat.factorial_mul_factorial_dvd_factorial_add m j)

/-- A finite tail of the exponential series, with the exact factorial prefactor. -/
theorem finite_poisson_tail {x : ℝ} (hx : 0 ≤ x) (m K : ℕ) :
    (∑ j ∈ Finset.range K, x ^ (m + j) / (m + j).factorial) ≤
      Real.exp x * x ^ m / m.factorial := by
  have hm : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  calc
    (∑ j ∈ Finset.range K, x ^ (m + j) / (m + j).factorial) ≤
        ∑ j ∈ Finset.range K, (x ^ m / m.factorial) * (x ^ j / j.factorial) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjpos : 0 < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
      calc
        x ^ (m + j) / (m + j).factorial ≤
            x ^ (m + j) / ((m.factorial : ℝ) * j.factorial) :=
          div_le_div_of_nonneg_left (pow_nonneg hx _) (mul_pos hm hjpos)
            (factorial_product_le m j)
        _ = (x ^ m / m.factorial) * (x ^ j / j.factorial) := by rw [pow_add]; ring
    _ = (x ^ m / m.factorial) * (∑ j ∈ Finset.range K, x ^ j / j.factorial) := by
      rw [Finset.mul_sum]
    _ ≤ (x ^ m / m.factorial) * Real.exp x :=
      mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx K) (by positivity)
    _ = Real.exp x * x ^ m / m.factorial := by ring

/-- The Poisson tail in the form used in Lemma 5.2. -/
theorem finite_poisson_tail_exp {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m) (K : ℕ) :
    (∑ j ∈ Finset.range K, x ^ (m + j) / (m + j).factorial) ≤
      Real.exp x * (Real.exp 1 * x / m) ^ m := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  apply (finite_poisson_tail hx m K).trans
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos x).le
  calc
    x ^ m / m.factorial ≤ x ^ m / ((m : ℝ) / Real.exp 1) ^ m :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) (pow_pos (div_pos hmpos (Real.exp_pos 1)) _)
        (factorial_lower_bound m)
    _ = (Real.exp 1 * x / m) ^ m := by
      rw [← div_pow]
      congr 1
      field_simp

end SpinGlass.SupportScalar
