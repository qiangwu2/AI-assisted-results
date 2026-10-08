import SpinGlass.Noise

/-!
# Product-kernel representation and symmetry of Boolean noise

These are exact finite-sum identities. The joint kernel includes one factor
`1/2` per coordinate and therefore represents uniform input signs. No analytic
reverse-hypercontractive inequality is assumed in this file.
-/

noncomputable section

namespace SpinGlass.NoiseKernel

open Finset
open SpinGlass.Noise SpinGlass.Expansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Translation on the Boolean cube by exclusive-or is its own inverse. -/
def xorTranslation (ε : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun ζ i := Bool.xor (ε i) (ζ i)
  invFun ζ i := Bool.xor (ε i) (ζ i)
  left_inv ζ := by
    funext i
    change Bool.xor (ε i) (Bool.xor (ε i) (ζ i)) = ζ i
    cases ε i <;> cases ζ i <;> rfl
  right_inv ζ := by
    funext i
    change Bool.xor (ε i) (Bool.xor (ε i) (ζ i)) = ζ i
    cases ε i <;> cases ζ i <;> rfl

/-- The transition probability from one cube point to another. -/
def cubeKernel (θ : ℝ) (ε η : ι → Bool) : ℝ :=
  ∏ i, noiseWeight θ (Bool.xor (ε i) (η i))

omit [DecidableEq ι] in
theorem cubeKernel_symmetric (θ : ℝ) (ε η : ι → Bool) :
    cubeKernel θ ε η = cubeKernel θ η ε := by
  unfold cubeKernel
  apply Finset.prod_congr rfl
  intro i hi
  rw [Bool.xor_comm]

/-- The original noise sum over sign multipliers equals a sum over output points. -/
theorem cubeNoise_eq_kernel_sum (θ : ℝ) (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    cubeNoise θ f ε = ∑ η : ι → Bool, cubeKernel θ ε η * f η := by
  unfold cubeNoise
  apply Fintype.sum_equiv (xorTranslation ε)
  intro ζ
  change (∏ i, noiseWeight θ (ζ i)) * f (fun i => Bool.xor (ε i) (ζ i)) =
    (∏ i, noiseWeight θ (Bool.xor (ε i) (Bool.xor (ε i) (ζ i)))) *
      f (fun i => Bool.xor (ε i) (ζ i))
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  cases ε i <;> cases ζ i <;> rfl

/-- The noise operator is self-adjoint for the unnormalized counting sum. -/
theorem cubeNoise_self_adjoint_sum (θ : ℝ) (f g : (ι → Bool) → ℝ) :
    (∑ ε : ι → Bool, f ε * cubeNoise θ g ε) =
      ∑ ε : ι → Bool, cubeNoise θ f ε * g ε := by
  simp_rw [cubeNoise_eq_kernel_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η hη
  apply Finset.sum_congr rfl
  intro ε hε
  rw [cubeKernel_symmetric θ ε η]
  ring

/-- Self-adjointness with exactly the manuscript's uniform expectation. -/
theorem cubeNoise_self_adjoint (θ : ℝ) (f g : (ι → Bool) → ℝ) :
    spinMean (fun ε => f ε * cubeNoise θ g ε) =
      spinMean (fun ε => cubeNoise θ f ε * g ε) := by
  unfold spinMean
  rw [cubeNoise_self_adjoint_sum]

/-- Constant product weights `∏ i, 1/2` are normalized on the Boolean cube. -/
theorem uniform_product_weights_sum :
    (∑ _ε : ι → Bool, ∏ _i : ι, (1 / 2 : ℝ)) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : ι) (_ : Bool) => (1 / 2 : ℝ))]
  norm_num

/-- The explicit product joint kernel pairs `f` with the noise of `g`. -/
theorem jointKernel_bilinear_eq (θ : ℝ) (f g : (ι → Bool) → ℝ) :
    (∑ ε : ι → Bool, ∑ η : ι → Bool,
      (∏ i, (1 / 2 : ℝ) * noiseWeight θ (Bool.xor (ε i) (η i))) * f ε * g η) =
        ∑ ε : ι → Bool, (∏ _i : ι, (1 / 2 : ℝ)) * f ε * cubeNoise θ g ε := by
  simp only [Finset.prod_mul_distrib, cubeNoise_eq_kernel_sum, cubeKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε hε
  apply Finset.sum_congr rfl
  intro η hη
  ring

/-- By symmetry, the same joint kernel pairs the noise of `f` with `g`.
This is the form needed to apply finite negative-moment duality. -/
theorem jointKernel_bilinear_eq_reverse (θ : ℝ) (f g : (ι → Bool) → ℝ) :
    (∑ ε : ι → Bool, ∑ η : ι → Bool,
      (∏ i, (1 / 2 : ℝ) * noiseWeight θ (Bool.xor (ε i) (η i))) * f ε * g η) =
        ∑ ε : ι → Bool, (∏ _i : ι, (1 / 2 : ℝ)) * cubeNoise θ f ε * g ε := by
  rw [jointKernel_bilinear_eq]
  calc
    (∑ ε : ι → Bool, (∏ i : ι, (1 / 2 : ℝ)) * f ε * cubeNoise θ g ε) =
        (∏ i : ι, (1 / 2 : ℝ)) * ∑ ε : ι → Bool, f ε * cubeNoise θ g ε := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ε hε
      ring
    _ = (∏ i : ι, (1 / 2 : ℝ)) * ∑ ε : ι → Bool, cubeNoise θ f ε * g ε := by
      rw [cubeNoise_self_adjoint_sum]
    _ = ∑ ε : ι → Bool, (∏ i : ι, (1 / 2 : ℝ)) * cubeNoise θ f ε * g ε := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ε hε
      ring

end SpinGlass.NoiseKernel
