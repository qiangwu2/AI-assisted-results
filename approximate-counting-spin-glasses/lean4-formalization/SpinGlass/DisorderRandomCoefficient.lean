import SpinGlass.DisorderSigns
import SpinGlass.ConditionalSpinGlass

/-!
# Magnitude-dependent coefficients under the original disorder law

The algorithm may choose a coefficient using the magnitudes (and separately
fixed internal randomness). Averaging over the original symmetric real iid
law still annihilates all cross terms. This file proves that fact for measurable
bounded coefficients, including the exact retained/random-coefficient error.
The boundedness is an explicit hypothesis on coefficients, not an assumed
mean-square error estimate.
-/
noncomputable section
namespace SpinGlass.Disorder
open scoped BigOperators
open MeasureTheory SpinGlass.Expansion SpinGlass.ConditionalSpinGlass
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Coordinate magnitudes; no sign is assigned to the zero atom. -/
def magnitudeArray (J : E → ℝ) : E → ℝ := fun e => |J e|

omit [Fintype E] [DecidableEq E] in
theorem continuous_magnitudeArray : Continuous (magnitudeArray (E := E)) :=
  continuous_pi (fun e => (continuous_apply e).abs)

omit [Fintype E] [DecidableEq E] in
theorem magnitudeArray_signedArray (J : E → ℝ) (η : E → Bool) :
    magnitudeArray (signedArray J η) = magnitudeArray J := by
  funext e
  simp [magnitudeArray, signedArray, abs_mul]

omit [Fintype E] [DecidableEq E] in
theorem monomial_signedArray (a : E → ℝ) (Γ : Finset E) (J : E → ℝ) (η : E → Bool) :
    monomial a Γ (signedArray J η) = monomial a Γ J * spinCharacter Γ η := by
  simp only [monomial, signedArray, weight, ← mul_assoc, tanh_mul_spinSign,
    Finset.prod_mul_distrib, spinCharacter]

/-- Polynomial whose graph coefficients may depend on all magnitudes. -/
def magnitudePolynomial (a : E → ℝ) (A : Finset (Finset E))
    (c : (E → ℝ) → Finset E → ℝ) (J : E → ℝ) : ℝ :=
  ∑ Γ ∈ A, c (magnitudeArray J) Γ * monomial a Γ J

/-- Finite sign orthogonality applies to magnitude-dependent coefficients. -/
theorem magnitudePolynomial_sign_second_moment (a : E → ℝ)
    (A : Finset (Finset E)) (c : (E → ℝ) → Finset E → ℝ) (J : E → ℝ) :
    spinMean (fun η => magnitudePolynomial a A c (signedArray J η) ^ 2) =
      ∑ Γ ∈ A, c (magnitudeArray J) Γ ^ 2 * monomial a Γ J ^ 2 := by
  simp only [magnitudePolynomial, magnitudeArray_signedArray, monomial_signedArray,
    ← mul_assoc]
  rw [SpinGlass.Expansion.polynomial_second_moment]
  simp only [mul_pow]

omit [Fintype E] [DecidableEq E] in
/-- Bounded coefficients give a bounded actual polynomial. -/
theorem abs_magnitudePolynomial_le (a : E → ℝ) (A : Finset (Finset E))
    (c : (E → ℝ) → Finset E → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x Γ, Γ ∈ A → |c x Γ| ≤ C) (J : E → ℝ) :
    |magnitudePolynomial a A c J| ≤ A.card * C := by
  calc
    _ ≤ ∑ Γ ∈ A, |c (magnitudeArray J) Γ * monomial a Γ J| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _Γ ∈ A, C := Finset.sum_le_sum fun Γ hΓ => by
      rw [abs_mul]
      exact (mul_le_mul (hbound _ Γ hΓ) (abs_monomial_le_one a Γ J)
        (abs_nonneg _) hC).trans_eq (mul_one C)
    _ = _ := by simp

/-- The exact diagonal identity for measurable magnitude-dependent graph
coefficients, integrated under the original iid symmetric real disorder. -/
theorem magnitudePolynomial_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (a : E → ℝ) (A : Finset (Finset E))
    (c : (E → ℝ) → Finset E → ℝ)
    (hc : ∀ Γ ∈ A, Measurable (fun x => c x Γ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x Γ, Γ ∈ A → |c x Γ| ≤ C) :
    (∫ J, magnitudePolynomial a A c J ^ 2 ∂iidLaw μ) =
      ∑ Γ ∈ A, ∫ J, c (magnitudeArray J) Γ ^ 2 * monomial a Γ J ^ 2 ∂iidLaw μ := by
  have hmeas : Measurable (magnitudePolynomial a A c) := by
    exact Finset.measurable_sum _ fun Γ hΓ =>
      ((hc Γ hΓ).comp continuous_magnitudeArray.measurable).mul
        (continuous_monomial a Γ).measurable
  have hsq : Integrable (fun J => magnitudePolynomial a A c J ^ 2) (iidLaw μ) := by
    refine Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable ((A.card * C) ^ 2) ?_
    apply ae_of_all
    intro J
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := abs_magnitudePolynomial_le a A c hC hbound J
    nlinarith [sq_abs (magnitudePolynomial a A c J), abs_nonneg (magnitudePolynomial a A c J)]
  have hterm (Γ : Finset E) (hΓ : Γ ∈ A) : Integrable
      (fun J => c (magnitudeArray J) Γ ^ 2 * monomial a Γ J ^ 2) (iidLaw μ) := by
    refine Integrable.of_bound
      ((((hc Γ hΓ).comp continuous_magnitudeArray.measurable).pow_const 2).mul
        ((continuous_monomial a Γ).measurable.pow_const 2)).aestronglyMeasurable (C ^ 2) ?_
    apply ae_of_all
    intro J
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hcB := hbound (magnitudeArray J) Γ hΓ
    have hmB := abs_monomial_le_one a Γ J
    have hcSq : c (magnitudeArray J) Γ ^ 2 ≤ C ^ 2 := by
      nlinarith [sq_abs (c (magnitudeArray J) Γ), abs_nonneg (c (magnitudeArray J) Γ)]
    have hmSq : monomial a Γ J ^ 2 ≤ 1 := by
      nlinarith [sq_abs (monomial a Γ J), abs_nonneg (monomial a Γ J)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hcSq) (sq_nonneg (monomial a Γ J))]
  rw [← integral_signMean_eq_of_integrable μ hμ _ hsq]
  simp_rw [magnitudePolynomial_sign_second_moment]
  exact integral_finsetSum A hterm


/-- Exact squared error between two magnitude-dependent graph polynomials.
The coefficient functions can encode arbitrary fixed algorithm randomness. -/
theorem magnitudePolynomial_error_second_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ) (a : E → ℝ)
    (A : Finset (Finset E)) (c d : (E → ℝ) → Finset E → ℝ)
    (hc : ∀ Γ ∈ A, Measurable (fun x => c x Γ))
    (hd : ∀ Γ ∈ A, Measurable (fun x => d x Γ))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcBound : ∀ x Γ, Γ ∈ A → |c x Γ| ≤ C)
    (hdBound : ∀ x Γ, Γ ∈ A → |d x Γ| ≤ D) :
    (∫ J, (magnitudePolynomial a A c J - magnitudePolynomial a A d J) ^ 2 ∂iidLaw μ) =
      ∑ Γ ∈ A, ∫ J,
        (c (magnitudeArray J) Γ - d (magnitudeArray J) Γ) ^ 2 * monomial a Γ J ^ 2 ∂iidLaw μ := by
  have heq (J : E → ℝ) :
      magnitudePolynomial a A c J - magnitudePolynomial a A d J =
        magnitudePolynomial a A (fun x Γ => c x Γ - d x Γ) J := by
    simp only [magnitudePolynomial, sub_mul, Finset.sum_sub_distrib]
  simp_rw [heq]
  apply magnitudePolynomial_second_moment μ hμ a A (fun x Γ => c x Γ - d x Γ)
    (fun Γ hΓ => (hc Γ hΓ).sub (hd Γ hΓ)) (add_nonneg hC hD)
  intro x Γ hΓ
  exact (abs_sub (c x Γ) (d x Γ)).trans (add_le_add (hcBound x Γ hΓ) (hdBound x Γ hΓ))

end SpinGlass.Disorder
