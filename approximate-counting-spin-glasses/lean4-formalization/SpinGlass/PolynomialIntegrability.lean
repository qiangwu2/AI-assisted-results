import SpinGlass.DisorderIndependentCoefficients

/-! Integrability obligations for finite graph-polynomial errors. -/

noncomputable section
namespace SpinGlass.PolynomialIntegrability
open Finset MeasureTheory
open SpinGlass.Disorder

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem continuous_polynomial (a : E → ℝ) (A : Finset (Finset E)) (c : Finset E → ℝ) :
    Continuous (fun J : E → ℝ => ∑ Γ ∈ A, c Γ * monomial a Γ J) := by
  exact continuous_finsetSum A (fun Γ _ => (continuous_monomial a Γ).const_mul (c Γ))

theorem integrable_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : E → ℝ) (A : Finset (Finset E)) (c : Finset E → ℝ) :
    Integrable (fun J : E → ℝ => (∑ Γ ∈ A, c Γ * monomial a Γ J)^2) (iidLaw μ) := by
  have heq : (fun J : E → ℝ => (∑ Γ ∈ A, c Γ * monomial a Γ J)^2) =
      (fun J => ∑ S ∈ A, ∑ T ∈ A, (c S*c T)*(monomial a S J*monomial a T J)) := by
    funext J
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    ring
  rw [heq]
  exact integrable_finsetSum A (fun S _ => integrable_finsetSum A
    (fun T _ => (integrable_monomial_mul μ a S T).const_mul _))

theorem integrable_difference_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : E → ℝ) (A D : Finset (Finset E)) (c d : Finset E → ℝ) :
    Integrable (fun J : E → ℝ =>
      ((∑ Γ ∈ A, c Γ * monomial a Γ J) - (∑ Γ ∈ D, d Γ * monomial a Γ J))^2) (iidLaw μ) := by
  have hc := integrable_square μ a A c
  have hd := integrable_square μ a D d
  have hprod := integrable_mul_of_integrable_squares (iidLaw μ)
    _ _ (continuous_polynomial a A c).measurable (continuous_polynomial a D d).measurable hc hd
  convert (hc.add hd).sub (hprod.const_mul 2) using 1
  funext J
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

end SpinGlass.PolynomialIntegrability
