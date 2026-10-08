import SpinGlass.ColoringProbability

/-!
# Exact variance reduction for independent finite coloring trials

All repetitions are sampled from the explicit uniform product space
`Fin R → (V → Fin L)`. Independence is derived from finite sums over this space.
-/

noncomputable section

namespace SpinGlass.ColoringRepetitions

open scoped BigOperators
open ColoringProbability

/-- Product averages factor on the actual finite independent-coordinate sample space. -/
theorem mean_pi_product {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (f : I → Ω → ℝ) :
    mean (fun ω : I → Ω => ∏ i, f i (ω i)) = ∏ i, mean (f i) := by
  classical
  simp only [mean, Fintype.card_fun, Nat.cast_pow, inv_pow]
  rw [← Fintype.prod_sum]
  rw [Finset.prod_mul_distrib]
  simp

/-- A single coordinate has its uniform marginal distribution. -/
theorem mean_eval {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (i : I) (f : Ω → ℝ) : mean (fun ω : I → Ω => f (ω i)) = mean f := by
  have h := mean_pi_product (fun j ω => if j = i then f ω else 1)
  have heq : (fun ω : I → Ω => ∏ j, if j = i then f (ω j) else (1 : ℝ)) =
      (fun ω => f (ω i)) := by funext ω; simp
  rw [heq] at h
  have hc : ∀ j : I, mean (fun ω : Ω => if j = i then f ω else 1) =
      if j = i then mean f else 1 := by
    intro j
    by_cases hj : j = i <;> simp [hj, mean_const]
  simp_rw [hc] at h
  simpa using h

/-- Two different repetitions are independent by exact product-space summation. -/
theorem mean_eval_mul {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (i j : I) (hij : i ≠ j) (f g : Ω → ℝ) :
    mean (fun ω : I → Ω => f (ω i) * g (ω j)) = mean f * mean g := by
  have h := mean_pi_product
    (fun k ω => (if k = i then f ω else 1) * (if k = j then g ω else 1))
  have heq : (fun ω : I → Ω => ∏ k,
      (if k = i then f (ω k) else 1) * (if k = j then g (ω k) else 1)) =
      (fun ω => f (ω i) * g (ω j)) := by
    funext ω
    rw [Finset.prod_mul_distrib]
    simp
  rw [heq] at h
  have hc : ∀ k : I, mean (fun ω : Ω =>
      (if k = i then f ω else 1) * (if k = j then g ω else 1)) =
      (if k = i then mean f else 1) * (if k = j then mean g else 1) := by
    intro k
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [mean_const]
  simp_rw [hc] at h
  rw [Finset.prod_mul_distrib] at h
  simpa using h

theorem mean_sum {I Ω : Type*} [Fintype Ω] (s : Finset I) (f : I → Ω → ℝ) :
    mean (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Exact second moment of a sum of independent centered copies. -/
theorem mean_sum_sq_centered {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (R : ℕ) (f : Ω → ℝ) (hf : mean f = 0) :
    mean (fun ω : Fin R → Ω => (∑ i, f (ω i)) ^ 2) =
      (R : ℝ) * mean (fun ω => f ω ^ 2) := by
  have hcross : ∀ i j : Fin R,
      mean (fun ω : Fin R → Ω => f (ω i) * f (ω j)) =
        if i = j then mean (fun ω => f ω ^ 2) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [if_true, pow_two] using mean_eval i (fun ω => f ω * f ω)
    · rw [mean_eval_mul i j hij, hf]
      simp [hij]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [mean_sum]
  simp_rw [mean_sum, hcross]
  simp [pow_two]

/-- Exact `1/R` variance reduction derived from the finite product distribution. -/
theorem mean_average_sq_centered {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {R : ℕ} (hR : 0 < R) (f : Ω → ℝ) (hf : mean f = 0) :
    mean (fun ω : Fin R → Ω => ((R : ℝ)⁻¹ * ∑ i, f (ω i)) ^ 2) =
      mean (fun ω => f ω ^ 2) / (R : ℝ) := by
  have hr : (R : ℝ) ≠ 0 := by positivity
  simp only [mul_pow]
  rw [mean_const_mul, mean_sum_sq_centered R f hf]
  field_simp

/-- The actual average of independent colorful graph coefficients. -/
def averageCoefficient {V : Type*} [Fintype V] (L R : ℕ)
    (χ : Fin R → (V → Fin L)) : ℝ :=
  (R : ℝ)⁻¹ * ∑ r, coefficient L (χ r)

/-- Independent repetition preserves exact unbiasedness. -/
theorem mean_averageCoefficient {V : Type*} [Fintype V] [DecidableEq V]
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (hm : Fintype.card V ≤ L) :
    mean (averageCoefficient (V := V) L R) = 1 := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have hr : (R : ℝ) ≠ 0 := by positivity
  unfold averageCoefficient
  rw [mean_const_mul, mean_sum]
  simp_rw [mean_eval, mean_coefficient hL hm]
  simp [hr]

/-- The repeated coefficient has exactly the variance stated in (83). -/
theorem mean_averageCoefficient_variance {V : Type*} [Fintype V] [DecidableEq V]
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (hm : Fintype.card V ≤ L) :
    mean (fun χ : Fin R → (V → Fin L) => (averageCoefficient L R χ - 1) ^ 2) =
      (1 - probability L (Fintype.card V)) /
        ((R : ℝ) * probability L (Fintype.card V)) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have hr : (R : ℝ) ≠ 0 := by positivity
  have hc : mean (fun χ : V → Fin L => coefficient L χ - 1) = 0 := by
    rw [mean_sub, mean_coefficient hL hm, mean_const]
    ring
  have hpoint : ∀ χ : Fin R → (V → Fin L), averageCoefficient L R χ - 1 =
      (R : ℝ)⁻¹ * ∑ r, (coefficient L (χ r) - 1) := by
    intro χ
    simp only [averageCoefficient, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  simp_rw [hpoint]
  rw [mean_average_sq_centered hR _ hc, mean_coefficient_variance hL hm]
  ring

/-- The final uniform coefficient variance bound includes the exact `1/R` gain. -/
theorem mean_averageCoefficient_variance_le {V : Type*} [Fintype V] [DecidableEq V]
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (hm : Fintype.card V ≤ L) :
    mean (fun χ : Fin R → (V → Fin L) => (averageCoefficient L R χ - 1) ^ 2) ≤
      Real.exp (L : ℝ) / (R : ℝ) := by
  rw [mean_averageCoefficient_variance hL hR hm]
  have hvar := mean_coefficient_variance_le_exp (V := V) hL hm
  rw [mean_coefficient_variance hL hm] at hvar
  have heq : (1 - probability L (Fintype.card V)) /
      ((R : ℝ) * probability L (Fintype.card V)) =
      ((1 - probability L (Fintype.card V)) / probability L (Fintype.card V)) / (R : ℝ) := by
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right hvar (by positivity)

end SpinGlass.ColoringRepetitions
