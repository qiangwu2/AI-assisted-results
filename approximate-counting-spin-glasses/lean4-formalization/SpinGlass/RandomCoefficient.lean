import SpinGlass.Expansion
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exact error identities with random coefficients

The outer variable may contain magnitudes and algorithm randomness; edge signs
are averaged independently by the explicit uniform cube mean. No independence
between different coefficient entries is needed. This is an iterated-expectation
identity. Constructing that sign/magnitude representation from the manuscript's
arbitrary symmetric real disorder is still a separate obligation.
-/

noncomputable section

namespace SpinGlass.RandomCoefficient

open scoped BigOperators
open MeasureTheory SpinGlass.Expansion

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Parseval applied to the actual difference of two sign polynomials. -/
theorem polynomial_error_second_moment (A : Finset (Finset E))
    (c d : Finset E → ℝ) :
    spinMean (fun η : E → Bool =>
      ((∑ Γ ∈ A, c Γ * spinCharacter Γ η) -
        (∑ Γ ∈ A, d Γ * spinCharacter Γ η)) ^ 2) =
      ∑ Γ ∈ A, (c Γ - d Γ) ^ 2 := by
  have heq : ∀ η : E → Bool,
      (∑ Γ ∈ A, c Γ * spinCharacter Γ η) -
        (∑ Γ ∈ A, d Γ * spinCharacter Γ η) =
      ∑ Γ ∈ A, (c Γ - d Γ) * spinCharacter Γ η := by
    intro η
    simp only [sub_mul, Finset.sum_sub_distrib]
  simp_rw [heq]
  exact polynomial_second_moment A (fun Γ => c Γ - d Γ)

/-- Averaging the exact sign error over an arbitrary outer measure preserves
the squared-coefficient identity. Integrability is required term by term. -/
theorem integrated_polynomial_error_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Finset (Finset E)) (c d : Ω → Finset E → ℝ)
    (hint : ∀ Γ ∈ A, Integrable (fun ω => (c ω Γ - d ω Γ) ^ 2) μ) :
    (∫ ω, spinMean (fun η : E → Bool =>
      ((∑ Γ ∈ A, c ω Γ * spinCharacter Γ η) -
        (∑ Γ ∈ A, d ω Γ * spinCharacter Γ η)) ^ 2) ∂μ) =
      ∑ Γ ∈ A, ∫ ω, (c ω Γ - d ω Γ) ^ 2 ∂μ := by
  simp_rw [polynomial_error_second_moment]
  exact integral_finsetSum A hint

/-- The retained-family error is exactly the mass of discarded characters.
`keep` is the actual membership test, not an assumed error estimate. -/
theorem retained_family_error (A : Finset (Finset E))
    (a : Finset E → ℝ) (keep : Finset E → Prop) [DecidablePred keep] :
    spinMean (fun η : E → Bool =>
      ((∑ Γ ∈ A, a Γ * spinCharacter Γ η) -
        (∑ Γ ∈ A.filter keep, a Γ * spinCharacter Γ η)) ^ 2) =
      ∑ Γ ∈ A.filter (fun Γ => ¬keep Γ), a Γ ^ 2 := by
  have hfilter : ∀ η : E → Bool,
      (∑ Γ ∈ A.filter keep, a Γ * spinCharacter Γ η) =
      ∑ Γ ∈ A, (if keep Γ then a Γ else 0) * spinCharacter Γ η := by
    intro η
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Γ hΓ
    split_ifs <;> simp
  simp_rw [hfilter]
  rw [polynomial_error_second_moment, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hk : keep Γ <;> simp [hk]

end SpinGlass.RandomCoefficient
