import SpinGlass.Expansion
import Mathlib.Tactic.Ring

/-!
# Finite independent-sign noise

The operator below is the explicit finite sum from the manuscript, using Boolean
coordinates for signs. The character identity is algebraic. No reverse
hypercontractive estimate is assumed or asserted here.
-/

namespace SpinGlass.Noise

noncomputable section

open Finset
open SpinGlass.Expansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A sign with mean `θ`, encoded as `false = +1` and `true = -1`. -/
def noiseWeight (θ : ℝ) (b : Bool) : ℝ :=
  if b then (1 - θ) / 2 else (1 + θ) / 2

/-- Independent-coordinate sign noise, written as a finite weighted sum. -/
def cubeNoise (θ : ℝ) (f : (ι → Bool) → ℝ) (ε : ι → Bool) : ℝ :=
  ∑ ζ : ι → Bool, (∏ i, noiseWeight θ (ζ i)) *
    f (fun i => Bool.xor (ε i) (ζ i))

theorem noiseWeight_sum (θ : ℝ) : (∑ b : Bool, noiseWeight θ b) = 1 := by
  simp [noiseWeight]
  ring

theorem noiseWeight_sign_sum (θ : ℝ) :
    (∑ b : Bool, noiseWeight θ b * spinSign b) = θ := by
  simp [noiseWeight, spinSign]
  ring

theorem noiseWeight_nonneg {θ : ℝ} (hθ : -1 ≤ θ) (hθ1 : θ ≤ 1) (b : Bool) :
    0 ≤ noiseWeight θ b := by
  cases b <;> simp only [noiseWeight, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem noiseWeight_pos {θ : ℝ} (hθ : -1 < θ) (hθ1 : θ < 1) (b : Bool) :
    0 < noiseWeight θ b := by
  cases b <;> simp only [noiseWeight, Bool.false_eq_true, ↓reduceIte] <;> linarith

/-- The finite product weights sum to one for every real parameter.
Together with `noiseWeight_nonneg`, they form a probability distribution when `-1 ≤ θ ≤ 1`. -/
theorem noiseWeight_normalization (θ : ℝ) :
    (∑ ζ : ι → Bool, ∏ i, noiseWeight θ (ζ i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [noiseWeight_sum, prod_const_one]

/-- Noise preserves strictly positive functions for parameters in `(-1,1)`. -/
theorem cubeNoise_pos {θ : ℝ} (hθ : -1 < θ) (hθ1 : θ < 1)
    (f : (ι → Bool) → ℝ) (hf : ∀ ε, 0 < f ε) (ε : ι → Bool) :
    0 < cubeNoise θ f ε := by
  apply Finset.sum_pos
  · intro ζ hζ
    exact mul_pos (Finset.prod_pos (fun i hi => noiseWeight_pos hθ hθ1 (ζ i))) (hf _)
  · exact Finset.univ_nonempty

/-- Multiplication of signs is Boolean exclusive-or. -/
theorem spinSign_xor (a b : Bool) : spinSign (Bool.xor a b) = spinSign a * spinSign b := by
  cases a <;> cases b <;> norm_num [spinSign]

omit [Fintype ι] [DecidableEq ι] in
theorem spinCharacter_xor (S : Finset ι) (ε ζ : ι → Bool) :
    spinCharacter S (fun i => Bool.xor (ε i) (ζ i)) =
      spinCharacter S ε * spinCharacter S ζ := by
  simp only [spinCharacter, spinSign_xor, Finset.prod_mul_distrib]

theorem spinCharacter_eq_full_product (S : Finset ι) (ζ : ι → Bool) :
    spinCharacter S ζ = ∏ i : ι, if i ∈ S then spinSign (ζ i) else 1 := by
  simp [spinCharacter]

/-- The product noise distribution has character moment `θ^|S|`. -/
theorem noise_character_moment (θ : ℝ) (S : Finset ι) :
    (∑ ζ : ι → Bool, (∏ i, noiseWeight θ (ζ i)) * spinCharacter S ζ) =
      θ ^ S.card := by
  simp_rw [spinCharacter_eq_full_product, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    noiseWeight θ b * (if i ∈ S then spinSign b else 1))]
  have hcoord : ∀ i : ι,
      (∑ b : Bool, noiseWeight θ b * (if i ∈ S then spinSign b else 1)) =
        if i ∈ S then θ else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simpa only [hi, ↓reduceIte] using noiseWeight_sign_sum θ
    · simpa only [hi, ↓reduceIte, mul_one] using noiseWeight_sum θ
  simp_rw [hcoord]
  rw [← Finset.prod_filter]
  simp

/-- Noise multiplies a sign monomial of degree `|S|` by `θ^|S|`. -/
theorem cubeNoise_character (θ : ℝ) (S : Finset ι) (ε : ι → Bool) :
    cubeNoise θ (spinCharacter S) ε = θ ^ S.card * spinCharacter S ε := by
  simp only [cubeNoise, spinCharacter_xor]
  calc
    (∑ ζ : ι → Bool, (∏ i, noiseWeight θ (ζ i)) *
        (spinCharacter S ε * spinCharacter S ζ)) =
        spinCharacter S ε *
          ∑ ζ : ι → Bool, (∏ i, noiseWeight θ (ζ i)) * spinCharacter S ζ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ζ hζ
      ring
    _ = spinCharacter S ε * θ ^ S.card := by rw [noise_character_moment]
    _ = θ ^ S.card * spinCharacter S ε := mul_comm _ _

theorem cubeNoise_mul_left (θ c : ℝ) (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    cubeNoise θ (fun ζ => c * f ζ) ε = c * cubeNoise θ f ε := by
  simp only [cubeNoise, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ζ hζ
  ring

theorem cubeNoise_sum {κ : Type*} (θ : ℝ) (T : Finset κ)
    (f : κ → (ι → Bool) → ℝ) (ε : ι → Bool) :
    cubeNoise θ (fun ζ => ∑ j ∈ T, f j ζ) ε = ∑ j ∈ T, cubeNoise θ (f j) ε := by
  simp only [cubeNoise, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Diagonal action on every finite sign polynomial. -/
theorem cubeNoise_polynomial (θ : ℝ) (A : Finset (Finset ι)) (c : Finset ι → ℝ)
    (ε : ι → Bool) :
    cubeNoise θ (fun ζ => ∑ S ∈ A, c S * spinCharacter S ζ) ε =
      ∑ S ∈ A, c S * θ ^ S.card * spinCharacter S ε := by
  rw [cubeNoise_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [cubeNoise_mul_left, cubeNoise_character]
  ring

/-- Coefficient inflation by `1/θ` is exactly undone by the noise operator. -/
theorem cubeNoise_inflated_polynomial (θ : ℝ) (hθ : θ ≠ 0)
    (A : Finset (Finset ι)) (b : ι → ℝ) (ε : ι → Bool) :
    cubeNoise θ
      (fun ζ => ∑ S ∈ A, (∏ i ∈ S, b i / θ) * spinCharacter S ζ) ε =
      ∑ S ∈ A, (∏ i ∈ S, b i) * spinCharacter S ε := by
  rw [cubeNoise_polynomial]
  apply Finset.sum_congr rfl
  intro S hS
  have hcoeff : (∏ i ∈ S, b i / θ) * θ ^ S.card = ∏ i ∈ S, b i := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hθ)
  rw [hcoeff]

omit [Fintype ι] [DecidableEq ι] in
/-- The inflated graphical sign polynomial is strictly positive under the
coefficient bound used on the manuscript's magnitude cutoff event. -/
theorem inflated_graphical_polynomial_pos {V : Type*} [Fintype V] [DecidableEq V]
    (incidence : ι → Finset V) (edges : Finset ι) (b : ι → ℝ) (θ : ℝ)
    (hbound : ∀ i ∈ edges, |b i / θ| ≤ 1 / 2) (ε : ι → Bool) :
    0 < ∑ S ∈ edges.powerset.filter (IsEven incidence),
      (∏ i ∈ S, b i / θ) * spinCharacter S ε := by
  simp only [spinCharacter, ← Finset.prod_mul_distrib]
  apply graphical_sum_pos incidence edges (fun i => (b i / θ) * spinSign (ε i))
  intro i hi
  simp only [abs_mul, abs_spinSign, mul_one]
  linarith [hbound i hi]

end

end SpinGlass.Noise
