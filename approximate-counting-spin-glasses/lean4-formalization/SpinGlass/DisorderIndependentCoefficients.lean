import SpinGlass.DisorderModel

/-!
# Square-integrable coefficients independent of disorder

This is the exact weighted Parseval identity on the actual product probability
space of algorithm randomness and arbitrary symmetric iid real disorder.
Only square integrability is required of the coefficients: they need not be
bounded. Integrability of every cross term is proved from that hypothesis.
-/
noncomputable section
namespace SpinGlass.Disorder
open scoped BigOperators
open MeasureTheory

variable {E Ω : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace Ω]

/-- The product of two square-integrable real functions is integrable. -/
theorem integrable_mul_of_integrable_squares (P : Measure Ω) (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfsq : Integrable (fun ω => f ω ^ 2) P)
    (hgsq : Integrable (fun ω => g ω ^ 2) P) :
    Integrable (fun ω => f ω * g ω) P := by
  refine ((hfsq.add hgsq).div_const 2).mono' (hf.mul hg).aestronglyMeasurable ?_
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_mul]
  dsimp only [Pi.add_apply]
  nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω)]

/-- Full weighted orthogonality for arbitrary square-integrable independent
random coefficients, integrated over the genuine product measure. -/
theorem independent_coefficients_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (P : Measure Ω) [IsProbabilityMeasure P]
    (a : E → ℝ) (A : Finset (Finset E)) (c : Ω → Finset E → ℝ)
    (hc : ∀ Γ ∈ A, Measurable (fun ω => c ω Γ))
    (hcsq : ∀ Γ ∈ A, Integrable (fun ω => c ω Γ ^ 2) P) :
    (∫ ωJ : Ω × (E → ℝ), (∑ Γ ∈ A, c ωJ.1 Γ * monomial a Γ ωJ.2) ^ 2
      ∂P.prod (iidLaw μ)) =
      ∑ Γ ∈ A, (∫ ω, c ω Γ ^ 2 ∂P) * ∏ e ∈ Γ, secondMoment μ (a e) := by
  have hint (S : Finset E) (hS : S ∈ A) (T : Finset E) (hT : T ∈ A) :
      Integrable (fun ωJ : Ω × (E → ℝ) =>
        (c ωJ.1 S * c ωJ.1 T) * (monomial a S ωJ.2 * monomial a T ωJ.2))
        (P.prod (iidLaw μ)) :=
    (integrable_mul_of_integrable_squares P (fun ω => c ω S) (fun ω => c ω T)
      (hc S hS) (hc T hT) (hcsq S hS) (hcsq T hT)).mul_prod
      (integrable_monomial_mul μ a S T)
  calc
    _ = ∫ ωJ : Ω × (E → ℝ), ∑ S ∈ A, ∑ T ∈ A,
        (c ωJ.1 S * c ωJ.1 T) * (monomial a S ωJ.2 * monomial a T ωJ.2)
        ∂P.prod (iidLaw μ) := by
      congr 1
      funext ωJ
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      ring
    _ = ∑ S ∈ A, ∑ T ∈ A, ∫ ωJ : Ω × (E → ℝ),
        (c ωJ.1 S * c ωJ.1 T) * (monomial a S ωJ.2 * monomial a T ωJ.2)
        ∂P.prod (iidLaw μ) := by
      rw [integral_finsetSum A (fun S hS => integrable_finsetSum A (fun T hT => hint S hS T hT))]
      apply Finset.sum_congr rfl
      intro S hS
      exact integral_finsetSum A (fun T hT => hint S hS T hT)
    _ = ∑ S ∈ A, ∑ T ∈ A,
        (∫ ω, c ω S * c ω T ∂P) *
          (if S = T then ∏ e ∈ S, secondMoment μ (a e) else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      rw [integral_prod_mul (fun ω => c ω S * c ω T)
        (fun J => monomial a S J * monomial a T J), monomial_orthogonality μ hμ]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [mul_ite, hS, sq]

/-- The corresponding exact squared-error identity. The only coefficient
moment assumption is the natural second moment of the actual coefficient error. -/
theorem independent_coefficient_error_second_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : E → ℝ) (A : Finset (Finset E)) (c d : Ω → Finset E → ℝ)
    (hcd : ∀ Γ ∈ A, Measurable (fun ω => c ω Γ - d ω Γ))
    (hcdsq : ∀ Γ ∈ A, Integrable (fun ω => (c ω Γ - d ω Γ) ^ 2) P) :
    (∫ ωJ : Ω × (E → ℝ),
      ((∑ Γ ∈ A, c ωJ.1 Γ * monomial a Γ ωJ.2) -
        (∑ Γ ∈ A, d ωJ.1 Γ * monomial a Γ ωJ.2)) ^ 2 ∂P.prod (iidLaw μ)) =
      ∑ Γ ∈ A, (∫ ω, (c ω Γ - d ω Γ) ^ 2 ∂P) * ∏ e ∈ Γ, secondMoment μ (a e) := by
  have heq (ωJ : Ω × (E → ℝ)) :
      (∑ Γ ∈ A, c ωJ.1 Γ * monomial a Γ ωJ.2) -
        (∑ Γ ∈ A, d ωJ.1 Γ * monomial a Γ ωJ.2) =
      ∑ Γ ∈ A, (c ωJ.1 Γ - d ωJ.1 Γ) * monomial a Γ ωJ.2 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  simp_rw [heq]
  exact independent_coefficients_second_moment μ hμ P a A (fun ω Γ => c ω Γ - d ω Γ) hcd hcdsq


/-- The product-law polynomial square is genuinely integrable under the natural
coefficient second-moment assumptions, independently of its integral identity. -/
theorem integrable_independent_polynomial_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : E → ℝ) (A : Finset (Finset E)) (c : Ω → Finset E → ℝ)
    (hc : ∀ Γ ∈ A, Measurable (fun ω => c ω Γ))
    (hcsq : ∀ Γ ∈ A, Integrable (fun ω => c ω Γ ^ 2) P) :
    Integrable (fun ωJ : Ω × (E → ℝ) => (∑ Γ ∈ A, c ωJ.1 Γ * monomial a Γ ωJ.2) ^ 2)
      (P.prod (iidLaw μ)) := by
  have hint (S : Finset E) (hS : S ∈ A) (T : Finset E) (hT : T ∈ A) :
      Integrable (fun ωJ : Ω × (E → ℝ) =>
        (c ωJ.1 S * c ωJ.1 T) * (monomial a S ωJ.2 * monomial a T ωJ.2))
        (P.prod (iidLaw μ)) :=
    (integrable_mul_of_integrable_squares P (fun ω => c ω S) (fun ω => c ω T)
      (hc S hS) (hc T hT) (hcsq S hS) (hcsq T hT)).mul_prod
      (integrable_monomial_mul μ a S T)
  have heq : (fun ωJ : Ω × (E → ℝ) => (∑ Γ ∈ A, c ωJ.1 Γ * monomial a Γ ωJ.2) ^ 2) =
      (fun ωJ : Ω × (E → ℝ) => ∑ S ∈ A, ∑ T ∈ A,
        (c ωJ.1 S * c ωJ.1 T) * (monomial a S ωJ.2 * monomial a T ωJ.2)) := by
    funext ωJ
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    ring
  rw [heq]
  exact integrable_finsetSum A (fun S hS => integrable_finsetSum A (fun T hT => hint S hS T hT))

end SpinGlass.Disorder
