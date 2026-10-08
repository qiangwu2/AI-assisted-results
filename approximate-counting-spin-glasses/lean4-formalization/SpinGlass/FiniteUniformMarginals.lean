import SpinGlass.FiniteProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import SpinGlass.ColorRestriction
import Mathlib.Probability.UniformOn

/-! Exact marginal laws for a finite independent uniform tape. -/
noncomputable section
namespace SpinGlass.FiniteProbability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Equality of every finite mean determines the whole pushforward measure. -/
theorem uniformLaw_map_of_mean {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (f : A → B)
    (h : ∀ g : B → ℝ, ColoringProbability.mean (fun a => g (f a)) = ColoringProbability.mean g) :
    (uniformLaw A).map f = uniformLaw B := by
  classical
  have hf : Measurable f := measurable_of_finite _
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hf hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi := h (S.indicator (fun _ => (1 : ℝ)))
  rw [← integral_uniformLaw, ← integral_uniformLaw] at hi
  have he : (fun a => S.indicator (fun _ => (1 : ℝ)) (f a)) =
      (f ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
    funext a
    simp only [Set.indicator_apply, Set.mem_preimage]
  rw [he, integral_indicator_const _ (hS.preimage hf), integral_indicator_const _ hS] at hi
  simpa only [smul_eq_mul, mul_one, Measure.real] using hi

theorem uniformLaw_eq_uniformOn (X : Type*) [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] : uniformLaw X = uniformOn (Set.univ : Set X) := by
  simp [uniformLaw, uniformOn, ProbabilityTheory.cond]

/-- Uniform vectors are precisely independent uniform coordinates. -/
theorem uniformLaw_pi {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
    [MeasurableSpace C] [MeasurableSingletonClass C] :
    uniformLaw (I → C) = Measure.pi (fun _ : I => uniformLaw C) := by
  simp only [uniformLaw_eq_uniformOn]
  simpa using (uniformOn_pi (f := fun _ : I => (Set.univ : Set C)))

/-- Restricting the tape to any set of queried positions gives exactly fresh
independent uniform samples on those positions. -/
theorem uniformLaw_restrict {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
    [Nonempty C] [MeasurableSpace C] [MeasurableSingletonClass C] (S : Finset I) :
    (uniformLaw (I → C)).map (fun χ => fun i : S => χ i) = uniformLaw (S → C) := by
  apply uniformLaw_map_of_mean
  intro g
  exact ColorRestriction.mean_restrict S g

end SpinGlass.FiniteProbability
