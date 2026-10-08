import SpinGlass.FiniteLowerTail
import SpinGlass.Partition

/-!
# Fixed-magnitude sign estimates for the spin-glass graph polynomial

For every fixed coefficient array satisfying the inflation cutoff, this file
proves the exact negative-moment and lower-tail bounds over independent uniform
edge signs, including their direct formulation for the normalized exponential
partition function. The right-hand side is the actual inflated even-graph mass,
not an assumed constant. Averaging over random magnitudes and estimating that
mass are separate obligations.
-/

noncomputable section

namespace SpinGlass.ConditionalSpinGlass

open Finset Real
open SpinGlass.Expansion SpinGlass.Noise SpinGlass.FiniteLowerTail SpinGlass.Partition

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The actual even-degree subgraphs of the specified edge family. -/
def evenGraphs (incidence : E → Finset V) (edges : Finset E) : Finset (Finset E) :=
  edges.powerset.filter (IsEven incidence)

/-- The high-temperature graph polynomial for fixed edge magnitudes and variable signs. -/
def graphPolynomial (incidence : E → Finset V) (edges : Finset E) (b : E → ℝ)
    (η : E → Bool) : ℝ :=
  ∑ Γ ∈ evenGraphs incidence edges, (∏ e ∈ Γ, b e) * spinCharacter Γ η

/-- Inflating every edge coefficient by `1/θ` gives the positive function used
as the input to reverse hypercontractivity. -/
def inflatedPolynomial (incidence : E → Finset V) (edges : Finset E)
    (θ : ℝ) (b : E → ℝ) : (E → Bool) → ℝ :=
  graphPolynomial incidence edges (fun e => b e / θ)

/-- The exact second-moment mass of the inflated graph polynomial. -/
def inflatedMass (incidence : E → Finset V) (edges : Finset E)
    (θ : ℝ) (b : E → ℝ) : ℝ :=
  ∑ Γ ∈ evenGraphs incidence edges, ∏ e ∈ Γ, (b e / θ) ^ 2

omit [Fintype E] [DecidableEq E] in
theorem empty_mem_evenGraphs (incidence : E → Finset V) (edges : Finset E) :
    ∅ ∈ evenGraphs incidence edges := by
  simp [evenGraphs, IsEven, degree]

/-- Independent edge signs annihilate every nonempty graph monomial. -/
theorem graphPolynomial_mean (incidence : E → Finset V) (edges : Finset E) (b : E → ℝ) :
    spinMean (graphPolynomial incidence edges b) = 1 := by
  change spinMean (fun η : E → Bool => ∑ Γ ∈ evenGraphs incidence edges,
    (∏ e ∈ Γ, b e) * spinCharacter Γ η) = 1
  have h := edge_subset_mean (evenGraphs incidence edges) b
  simpa only [spinCharacter, Finset.prod_mul_distrib,
    if_pos (empty_mem_evenGraphs incidence edges)] using h

theorem inflatedPolynomial_mean (incidence : E → Finset V) (edges : Finset E)
    (θ : ℝ) (b : E → ℝ) :
    spinMean (inflatedPolynomial incidence edges θ b) = 1 :=
  graphPolynomial_mean incidence edges (fun e => b e / θ)

omit [Fintype E] [DecidableEq E] in
/-- The cutoff makes the inflated polynomial strictly positive at every sign configuration. -/
theorem inflatedPolynomial_pos (incidence : E → Finset V) (edges : Finset E)
    (θ : ℝ) (b : E → ℝ) (hbound : ∀ e ∈ edges, |b e / θ| ≤ 1 / 2)
    (η : E → Bool) : 0 < inflatedPolynomial incidence edges θ b η := by
  exact inflated_graphical_polynomial_pos incidence edges b θ hbound η

/-- Noise cancels the coefficient inflation on the actual even-graph polynomial. -/
theorem noise_inflatedPolynomial (incidence : E → Finset V) (edges : Finset E)
    (θ : ℝ) (hθ : θ ≠ 0) (b : E → ℝ) (η : E → Bool) :
    cubeNoise θ (inflatedPolynomial incidence edges θ b) η =
      graphPolynomial incidence edges b η := by
  exact cubeNoise_inflated_polynomial θ hθ (evenGraphs incidence edges) b η

/-- Orthogonality gives the exact inflated graph mass, without an upper-bound assumption. -/
theorem inflatedPolynomial_second_moment (incidence : E → Finset V) (edges : Finset E)
    (θ : ℝ) (b : E → ℝ) :
    spinMean (fun η => (inflatedPolynomial incidence edges θ b η) ^ 2) =
      inflatedMass incidence edges θ b := by
  simpa only [inflatedPolynomial, graphPolynomial, inflatedMass,
    spinCharacter, Finset.prod_mul_distrib] using
    edge_subset_second_moment (evenGraphs incidence edges) (fun e => b e / θ)

omit [Fintype E] [DecidableEq E] in
/-- The graph mass is nonnegative for every coefficient array, including outside the cutoff. -/
theorem inflatedMass_nonneg (incidence : E → Finset V) (edges : Finset E)
    (θ : ℝ) (b : E → ℝ) : 0 ≤ inflatedMass incidence edges θ b := by
  exact Finset.sum_nonneg (fun Γ hΓ => Finset.prod_nonneg (fun e he => sq_nonneg _))

omit [Fintype E] [DecidableEq E] in
/-- The empty graph contributes one to the mass, and every other contribution is nonnegative. -/
theorem one_le_inflatedMass (incidence : E → Finset V) (edges : Finset E)
    (θ : ℝ) (b : E → ℝ) : 1 ≤ inflatedMass incidence edges θ b := by
  have h := Finset.single_le_sum
    (f := fun Γ : Finset E => ∏ e ∈ Γ, (b e / θ) ^ 2)
    (fun Γ hΓ => Finset.prod_nonneg (fun e he => sq_nonneg _))
    (empty_mem_evenGraphs incidence edges)
  simpa only [Finset.prod_empty, inflatedMass] using h

/-- Positivity of the original graph polynomial follows from its positive noise representation. -/
theorem graphPolynomial_pos (incidence : E → Finset V) (edges : Finset E)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (b : E → ℝ)
    (hbound : ∀ e ∈ edges, |b e / θ| ≤ 1 / 2) (η : E → Bool) :
    0 < graphPolynomial incidence edges b η := by
  rw [← noise_inflatedPolynomial incidence edges θ hθ.ne' b η]
  exact cubeNoise_pos (by linarith) hθ1 (inflatedPolynomial incidence edges θ b)
    (inflatedPolynomial_pos incidence edges θ b hbound) η

/-- For each fixed magnitude array satisfying the cutoff, the negative sign
moment of the original polynomial is bounded by the exact inflated graph mass. -/
theorem fixed_magnitude_negative_moment (incidence : E → Finset V) (edges : Finset E)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (b : E → ℝ)
    (hbound : ∀ e ∈ edges, |b e / θ| ≤ 1 / 2) :
    spinMean (fun η => (graphPolynomial incidence edges b η) ^
        (-((1 - Real.sqrt θ) / Real.sqrt θ))) ≤
      inflatedMass incidence edges θ b := by
  have h := noisy_negative_moment_le_second_moment hθ hθ1
    (inflatedPolynomial incidence edges θ b)
    (inflatedPolynomial_pos incidence edges θ b hbound)
    (inflatedPolynomial_mean incidence edges θ b)
  simpa only [noise_inflatedPolynomial incidence edges θ hθ.ne' b,
    inflatedPolynomial_second_moment] using h

/-- The actual uniform proportion of edge-sign configurations in the lower tail. -/
theorem fixed_magnitude_lower_tail (incidence : E → Finset V) (edges : Finset E)
    {θ z : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z) (b : E → ℝ)
    (hbound : ∀ e ∈ edges, |b e / θ| ≤ 1 / 2) :
    ((Finset.univ.filter
      (fun η : E → Bool => graphPolynomial incidence edges b η < z)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card E ≤
      inflatedMass incidence edges θ b * z ^ ((1 - Real.sqrt θ) / Real.sqrt θ) := by
  have h := noisy_lower_tail_le_second_moment hθ hθ1 hz
    (inflatedPolynomial incidence edges θ b)
    (inflatedPolynomial_pos incidence edges θ b hbound)
    (inflatedPolynomial_mean incidence edges θ b)
  simpa only [noise_inflatedPolynomial incidence edges θ hθ.ne' b,
    inflatedPolynomial_second_moment] using h

/-- Hyperbolic tangent transports an edge sign to the coefficient of its graph monomial. -/
theorem tanh_mul_spinSign (x : ℝ) (b : Bool) :
    Real.tanh (x * spinSign b) = Real.tanh x * spinSign b := by
  cases b <;> simp [spinSign, Real.tanh_neg]

omit [Fintype E] [DecidableEq E] in
/-- The normalized exponential partition function with variable edge signs is
exactly the graph polynomial used in the fixed-magnitude estimates. -/
theorem normalizedPartition_eq_graphPolynomial
    (incidence : E → Finset V) (edges : Finset E) (x : E → ℝ) (η : E → Bool) :
    normalizedPartition incidence edges (fun e => x e * spinSign (η e)) =
      graphPolynomial incidence edges (fun e => Real.tanh (x e)) η := by
  rw [normalizedPartition_eq_even_sum]
  simp only [tanh_mul_spinSign, graphPolynomial, evenGraphs,
    spinCharacter, Finset.prod_mul_distrib]

/-- The negative-moment bound directly for the normalized exponential partition
function, with its exact inflated graph mass on the right. -/
theorem normalizedPartition_negative_moment
    (incidence : E → Finset V) (edges : Finset E) {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (x : E → ℝ)
    (hbound : ∀ e ∈ edges, |Real.tanh (x e) / θ| ≤ 1 / 2) :
    spinMean (fun η : E → Bool =>
      (normalizedPartition incidence edges (fun e => x e * spinSign (η e))) ^
        (-((1 - Real.sqrt θ) / Real.sqrt θ))) ≤
      inflatedMass incidence edges θ (fun e => Real.tanh (x e)) := by
  simpa only [normalizedPartition_eq_graphPolynomial] using
    fixed_magnitude_negative_moment incidence edges hθ hθ1
      (fun e => Real.tanh (x e)) hbound

/-- The actual uniform sign probability of a small normalized exponential
partition function, without an assumed lower-tail or graph-mass bound. -/
theorem normalizedPartition_lower_tail
    (incidence : E → Finset V) (edges : Finset E) {θ z : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z) (x : E → ℝ)
    (hbound : ∀ e ∈ edges, |Real.tanh (x e) / θ| ≤ 1 / 2) :
    ((Finset.univ.filter (fun η : E → Bool =>
      normalizedPartition incidence edges (fun e => x e * spinSign (η e)) < z)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card E ≤
      inflatedMass incidence edges θ (fun e => Real.tanh (x e)) *
        z ^ ((1 - Real.sqrt θ) / Real.sqrt θ) := by
  simpa only [normalizedPartition_eq_graphPolynomial] using
    fixed_magnitude_lower_tail incidence edges hθ hθ1 hz
      (fun e => Real.tanh (x e)) hbound

end SpinGlass.ConditionalSpinGlass
