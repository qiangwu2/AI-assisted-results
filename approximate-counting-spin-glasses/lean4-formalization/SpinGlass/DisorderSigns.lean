import SpinGlass.DisorderModel
import SpinGlass.NoiseKernel

/-!
# Sign randomization of general symmetric disorder

Every bounded measurable observable has the same expectation after adjoining
independent uniform edge signs. Replacing each real coefficient by its absolute
value inside this sign average has no effect. The proof includes arbitrary mass
at zero and proves the representation from symmetry of the original law.
-/
noncomputable section
namespace SpinGlass.Disorder
open scoped BigOperators
open MeasureTheory SpinGlass.Expansion SpinGlass.Noise SpinGlass.NoiseKernel

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Multiply the disorder coordinates by the independently chosen signs. -/
def signedArray (J : E → ℝ) (η : E → Bool) : E → ℝ :=
  fun e => J e * spinSign (η e)

omit [Fintype E] [DecidableEq E] in
theorem continuous_signedArray (η : E → Bool) :
    Continuous (fun J : E → ℝ => signedArray J η) := by
  exact continuous_pi fun e => (continuous_apply e).mul continuous_const

omit [DecidableEq E] in
/-- Every fixed sign change preserves the complete iid disorder law. -/
theorem measurePreserving_signedArray (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (η : E → Bool) :
    MeasurePreserving (fun J : E → ℝ => signedArray J η) (iidLaw μ) (iidLaw μ) := by
  change MeasurePreserving (fun (J : E → ℝ) e => J e * spinSign (η e))
    (Measure.pi (fun _ : E => μ)) (Measure.pi (fun _ : E => μ))
  apply measurePreserving_pi (fun _ : E => μ) (fun _ : E => μ)
    (f := fun e x => x * spinSign (η e))
  intro e
  cases hη : η e
  · refine ⟨by fun_prop, ?_⟩
    simp [spinSign]
  · refine ⟨by fun_prop, ?_⟩
    simpa only [SymmetricLaw, spinSign, if_true, mul_neg_one] using hμ

/-- Pointwise equality of sign averages for real coordinates and their
magnitudes. Zero coordinates require no special conditional-probability convention. -/
theorem signMean_abs_eq (J : E → ℝ) (F : (E → ℝ) → ℝ) :
    spinMean (fun η => F (signedArray (fun e => |J e|) η)) =
      spinMean (fun η => F (signedArray J η)) := by
  unfold spinMean
  congr 1
  let ε : E → Bool := fun e => decide (J e < 0)
  apply Fintype.sum_equiv (xorTranslation ε)
  intro η
  congr 1
  funext e
  change |J e| * spinSign (η e) = J e * spinSign (Bool.xor (ε e) (η e))
  rw [spinSign_xor]
  by_cases hJ : J e < 0
  · simp [ε, hJ, spinSign, abs_of_neg hJ]
  · simp [ε, hJ, spinSign, abs_of_nonneg (le_of_not_gt hJ)]


/-- Sign randomization also holds for every integrable observable; no uniform
bound on the observable is required. -/
theorem integral_signMean_eq_of_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (F : (E → ℝ) → ℝ) (hF : Integrable F (iidLaw μ)) :
    (∫ J, spinMean (fun η => F (signedArray J η)) ∂iidLaw μ) =
      ∫ J, F J ∂iidLaw μ := by
  have hint (η : E → Bool) : Integrable (fun J => F (signedArray J η)) (iidLaw μ) :=
    (measurePreserving_signedArray μ hμ η).integrable_comp_of_integrable hF
  have heq (η : E → Bool) : (∫ J, F (signedArray J η) ∂iidLaw μ) =
      ∫ J, F J ∂iidLaw μ := by
    have hFm : AEStronglyMeasurable F
        ((iidLaw μ).map (fun J => signedArray J η)) := by
      rw [(measurePreserving_signedArray μ hμ η).map_eq]
      exact hF.aestronglyMeasurable
    have h := integral_map (μ := iidLaw μ)
      (measurePreserving_signedArray μ hμ η).measurable.aemeasurable hFm
    rw [(measurePreserving_signedArray μ hμ η).map_eq] at h
    exact h.symm
  unfold spinMean
  rw [integral_const_mul, integral_finsetSum _ (fun η _ => hint η)]
  simp_rw [heq]
  simp

/-- The original disorder expectation equals the average after independently
randomizing every sign. This is proved from the original law, not assumed. -/
theorem integral_signMean_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (F : (E → ℝ) → ℝ) (hF : Measurable F)
    (C : ℝ) (hbound : ∀ J, ‖F J‖ ≤ C) :
    (∫ J, spinMean (fun η => F (signedArray J η)) ∂iidLaw μ) =
      ∫ J, F J ∂iidLaw μ := by
  have hint (η : E → Bool) : Integrable (fun J => F (signedArray J η)) (iidLaw μ) :=
    Integrable.of_bound
      (hF.comp (continuous_signedArray η).measurable).aestronglyMeasurable C
      (ae_of_all _ fun J => hbound _)
  have heq (η : E → Bool) : (∫ J, F (signedArray J η) ∂iidLaw μ) =
      ∫ J, F J ∂iidLaw μ := by
    have h := integral_map (μ := iidLaw μ)
      (measurePreserving_signedArray μ hμ η).measurable.aemeasurable
      hF.aestronglyMeasurable
    rw [(measurePreserving_signedArray μ hμ η).map_eq] at h
    exact h.symm
  unfold spinMean
  rw [integral_const_mul, integral_finsetSum _ (fun η _ => hint η)]
  simp_rw [heq]
  simp

/-- Full sign/magnitude expectation representation for any bounded measurable
observable, valid also for discrete symmetric laws and atoms at zero. -/
theorem integral_magnitude_signMean_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (F : (E → ℝ) → ℝ) (hF : Measurable F)
    (C : ℝ) (hbound : ∀ J, ‖F J‖ ≤ C) :
    (∫ J, spinMean (fun η => F (signedArray (fun e => |J e|) η)) ∂iidLaw μ) =
      ∫ J, F J ∂iidLaw μ := by
  simp_rw [signMean_abs_eq]
  exact integral_signMean_eq μ hμ F hF C hbound


/-- The full sign/magnitude representation for all integrable observables. -/
theorem integral_magnitude_signMean_eq_of_integrable (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (F : (E → ℝ) → ℝ) (hF : Integrable F (iidLaw μ)) :
    (∫ J, spinMean (fun η => F (signedArray (fun e => |J e|) η)) ∂iidLaw μ) =
      ∫ J, F J ∂iidLaw μ := by
  simp_rw [signMean_abs_eq]
  exact integral_signMean_eq_of_integrable μ hμ F hF

end SpinGlass.Disorder
