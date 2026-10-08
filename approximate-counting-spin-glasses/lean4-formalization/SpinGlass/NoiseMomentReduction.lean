import SpinGlass.NoiseKernel
import SpinGlass.ReverseHolder

/-!
# From a cube bilinear estimate to a negative moment

This file composes explicit kernel symmetry with finite weighted duality. Its
bilinear hypothesis is explicit. The `ReverseHypercontractivity` module supplies
the proved scalar and tensorized estimates and discharges this hypothesis.
-/

namespace SpinGlass.NoiseMomentReduction

open Finset Real
open SpinGlass.Noise SpinGlass.NoiseKernel SpinGlass.ReverseHolder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact negative-moment consequence of a positive-exponent bilinear estimate
for the explicit product noise kernel. The statement assumes that estimate and
does not assert that any particular noise parameter satisfies it. -/
theorem negative_moment_of_cube_bilinear (θ r s : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hs : 0 < s)
    (f : (ι → Bool) → ℝ) (hf : ∀ ε, 0 < f ε)
    (hbilinear : ∀ g : (ι → Bool) → ℝ, (∀ ε, 0 < g ε) →
      (∑ ε : ι → Bool, (∏ _i : ι, (1 / 2 : ℝ)) * f ε ^ r) ^ (1 / r) *
        (∑ ε : ι → Bool, (∏ _i : ι, (1 / 2 : ℝ)) * g ε ^ (s / (1 + s))) ^
          (1 / (s / (1 + s))) ≤
        ∑ ε : ι → Bool, ∑ η : ι → Bool,
          (∏ i, (1 / 2 : ℝ) * noiseWeight θ (Bool.xor (ε i) (η i))) * f ε * g η) :
    (∑ ε : ι → Bool, (∏ _i : ι, (1 / 2 : ℝ)) * (cubeNoise θ f ε) ^ (-s)) ≤
      (∑ ε : ι → Bool, (∏ _i : ι, (1 / 2 : ℝ)) * f ε ^ r) ^ (-s / r) := by
  let w : (ι → Bool) → ℝ := fun _ => ∏ i : ι, (1 / 2 : ℝ)
  have hw : ∀ ε ∈ (Finset.univ : Finset (ι → Bool)), 0 ≤ w ε := by
    intro ε hε
    exact Finset.prod_nonneg (fun i hi => by norm_num)
  have hw1 : ∑ ε : ι → Bool, w ε = 1 := uniform_product_weights_sum
  have hmoment : 0 < ∑ ε : ι → Bool, w ε * f ε ^ r :=
    weighted_rpow_sum_pos Finset.univ w f hw hw1 (fun ε hε => hf ε) r
  have hK : 0 < (∑ ε : ι → Bool, w ε * f ε ^ r) ^ (1 / r) :=
    Real.rpow_pos_of_pos hmoment _
  have hnoise : ∀ ε ∈ (Finset.univ : Finset (ι → Bool)), 0 < cubeNoise θ f ε := by
    intro ε hε
    exact cubeNoise_pos (by linarith) hθ1 f hf ε
  have hbound := negative_moment_of_bilinear Finset.univ w (cubeNoise θ f)
    hw hw1 hnoise hs hK (by
      intro g hg
      have hb := hbilinear g (fun ε => hg ε (Finset.mem_univ ε))
      rw [jointKernel_bilinear_eq_reverse] at hb
      exact hb)
  change (∑ ε : ι → Bool, w ε * (cubeNoise θ f ε) ^ (-s)) ≤
    (∑ ε : ι → Bool, w ε * f ε ^ r) ^ (-s / r)
  calc
    (∑ ε : ι → Bool, w ε * (cubeNoise θ f ε) ^ (-s)) ≤
        ((∑ ε : ι → Bool, w ε * f ε ^ r) ^ (1 / r)) ^ (-s) := hbound
    _ = (∑ ε : ι → Bool, w ε * f ε ^ r) ^ (-s / r) := by
      rw [← Real.rpow_mul hmoment.le]
      congr 1
      ring

end SpinGlass.NoiseMomentReduction
