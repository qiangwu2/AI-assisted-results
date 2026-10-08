import SpinGlass.ColorRestriction
import SpinGlass.RandomCoefficient

/-!
# Signed colorful-estimator mean and error on the actual finite color space

Each branching-set label has an independent array of vertex colors. Graphs using
the same label share that array and may have arbitrarily correlated indicators.
Sign orthogonality, not independence between graphs, gives the error estimate.
The connection of this graph-sum estimator to the fast primitive evaluator is a
separate combinatorial obligation.
-/

noncomputable section

namespace SpinGlass.ColoringEstimator

open scoped BigOperators
open ColoringProbability ColoringRepetitions ColorRestriction Expansion RandomCoefficient

variable {V E B : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- One global color array per candidate branching set and per repetition. -/
abbrev Colors (V B : Type*) (L R : ℕ) := B → Fin R → V → Fin L

/-- The actual coefficient assigned to a graph by its branching-set color trials. -/
def graphCoefficient (outside : Finset E → Finset V) (branch : Finset E → B)
    (L R : ℕ) (χ : Colors V B L R) (Γ : Finset E) : ℝ :=
  supportCoefficient (outside Γ) L R (χ (branch Γ))

/-- Explicit signed graph-sum estimator. -/
def estimator (A : Finset (Finset E)) (a : Finset E → ℝ)
    (outside : Finset E → Finset V) (branch : Finset E → B)
    (L R : ℕ) (χ : Colors V B L R) (η : E → Bool) : ℝ :=
  ∑ Γ ∈ A, (graphCoefficient outside branch L R χ Γ * a Γ) * spinCharacter Γ η

theorem mean_graphCoefficient (outside : Finset E → Finset V) (branch : Finset E → B)
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (Γ : Finset E)
    (hΓ : (outside Γ).card ≤ L) :
    mean (fun χ : Colors V B L R => graphCoefficient outside branch L R χ Γ) = 1 := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  unfold graphCoefficient
  rw [mean_eval]
  exact mean_supportCoefficient (outside Γ) hL hR hΓ

theorem mean_graphCoefficient_variance (outside : Finset E → Finset V)
    (branch : Finset E → B) {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (Γ : Finset E) (hΓ : (outside Γ).card ≤ L) :
    mean (fun χ : Colors V B L R => (graphCoefficient outside branch L R χ Γ - 1) ^ 2) =
      (1 - probability L (outside Γ).card) /
        ((R : ℝ) * probability L (outside Γ).card) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  unfold graphCoefficient
  rw [mean_eval (branch Γ) (fun χ => (supportCoefficient (outside Γ) L R χ - 1) ^ 2)]
  exact mean_supportCoefficient_variance (outside Γ) hL hR hΓ

theorem mean_graphCoefficient_variance_le (outside : Finset E → Finset V)
    (branch : Finset E → B) {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (Γ : Finset E) (hΓ : (outside Γ).card ≤ L) :
    mean (fun χ : Colors V B L R => (graphCoefficient outside branch L R χ Γ - 1) ^ 2) ≤
      Real.exp (L : ℝ) / (R : ℝ) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  unfold graphCoefficient
  rw [mean_eval (branch Γ) (fun χ => (supportCoefficient (outside Γ) L R χ - 1) ^ 2)]
  exact mean_supportCoefficient_variance_le (outside Γ) hL hR hΓ

/-- Exact conditional unbiasedness, for arbitrary fixed signed graph weights. -/
theorem estimator_unbiased (A : Finset (Finset E)) (a : Finset E → ℝ)
    (outside : Finset E → Finset V) (branch : Finset E → B)
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hA : ∀ Γ ∈ A, (outside Γ).card ≤ L) (η : E → Bool) :
    mean (fun χ : Colors V B L R => estimator A a outside branch L R χ η) =
      ∑ Γ ∈ A, a Γ * spinCharacter Γ η := by
  unfold estimator
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [mean_mul_const, mean_mul_const, mean_graphCoefficient outside branch hL hR Γ (hA Γ hΓ)]
  simp

/-- The exact signed estimator variance, retaining the graph-specific probabilities. -/
theorem estimator_error_exact (A : Finset (Finset E)) (a : Finset E → ℝ)
    (outside : Finset E → Finset V) (branch : Finset E → B)
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hA : ∀ Γ ∈ A, (outside Γ).card ≤ L) :
    mean (fun χ : Colors V B L R => spinMean (fun η : E → Bool =>
      (estimator A a outside branch L R χ η -
        ∑ Γ ∈ A, a Γ * spinCharacter Γ η) ^ 2)) =
      ∑ Γ ∈ A, a Γ ^ 2 *
        ((1 - probability L (outside Γ).card) /
          ((R : ℝ) * probability L (outside Γ).card)) := by
  unfold estimator
  simp_rw [polynomial_error_second_moment]
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  have hpoint : (fun χ : Colors V B L R =>
      (graphCoefficient outside branch L R χ Γ * a Γ - a Γ) ^ 2) =
      (fun χ => a Γ ^ 2 * (graphCoefficient outside branch L R χ Γ - 1) ^ 2) := by
    funext χ
    ring
  rw [hpoint, mean_const_mul,
    mean_graphCoefficient_variance outside branch hL hR Γ (hA Γ hΓ)]

/-- The coloring part of (82), with the actual retained squared mass on the right. -/
theorem estimator_error_le (A : Finset (Finset E)) (a : Finset E → ℝ)
    (outside : Finset E → Finset V) (branch : Finset E → B)
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hA : ∀ Γ ∈ A, (outside Γ).card ≤ L) :
    mean (fun χ : Colors V B L R => spinMean (fun η : E → Bool =>
      (estimator A a outside branch L R χ η -
        ∑ Γ ∈ A, a Γ * spinCharacter Γ η) ^ 2)) ≤
      (Real.exp (L : ℝ) / (R : ℝ)) * ∑ Γ ∈ A, a Γ ^ 2 := by
  rw [estimator_error_exact A a outside branch hL hR hA, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Γ hΓ
  have hv := mean_graphCoefficient_variance_le outside branch hL hR Γ (hA Γ hΓ)
  rw [mean_graphCoefficient_variance outside branch hL hR Γ (hA Γ hΓ)] at hv
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hv (sq_nonneg (a Γ))

end SpinGlass.ColoringEstimator
