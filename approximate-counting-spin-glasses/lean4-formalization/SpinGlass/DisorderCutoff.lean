import SpinGlass.DisorderLowerTail
import SpinGlass.DisorderMomentBounds
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The manuscript's raw-disorder cutoff

The one-edge inflation event is bounded by the original law beyond
`artanh (θ/2) / a`. Thus the integrated lower tail has exactly the usual
number-of-edges times raw-disorder-tail remainder, with no tail assumption.
-/
noncomputable section
namespace SpinGlass.Disorder
open MeasureTheory Set

/-- Monotonicity follows from the verified inverse function on (-1,1). -/
theorem tanh_monotone : Monotone Real.tanh := by
  intro x y hxy
  have h := (Real.artanh_le_artanh_iff
    (show Real.tanh x ∈ Ioo (-1) 1 from ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩)
    (show Real.tanh y ∈ Ioo (-1) 1 from ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩)).mp
  exact h (by simpa only [Real.artanh_tanh] using hxy)

theorem abs_tanh_eq_tanh_abs (x : ℝ) : |Real.tanh x| = Real.tanh |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le
  · have hs : Real.tanh x ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hx) (Real.cosh_pos x).le
    rw [abs_of_nonpos hx, Real.tanh_neg, abs_of_nonpos hs]

/-- The exact raw-disorder threshold used by the paper ensures inflation. -/
theorem weight_inflation_le_half_of_abs_le {a θ x : ℝ}
    (ha : 0 < a) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hx : |x| ≤ Real.artanh (θ / 2) / a) : |weight a x / θ| ≤ 1 / 2 := by
  have hax : |a * x| ≤ Real.artanh (θ / 2) := by
    rw [abs_mul, abs_of_pos ha]
    simpa only [mul_comm a |x|] using (le_div_iff₀ ha).mp hx
  have ht : |weight a x| ≤ θ / 2 := by
    rw [weight, abs_tanh_eq_tanh_abs]
    have h := tanh_monotone hax
    rwa [Real.tanh_artanh (show θ / 2 ∈ Ioo (-1) 1 from ⟨by linarith, by linarith⟩)] at h
  rw [abs_div, abs_of_pos hθ]
  exact (div_le_iff₀ hθ).mpr (by linarith)

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]

/-- The paper's τ term: number of interactions times the raw one-edge tail. -/
def disorderTailRemainder (μ : Measure ℝ) (edges : Finset E) (a θ : ℝ) : ℝ :=
  edges.card * μ.real {x : ℝ | Real.artanh (θ / 2) / a < |x|}

/-- Failed inflation is controlled by the explicit τ term of the original law. -/
theorem inflationCutoff_failure_le_remainder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (edges : Finset E) {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hθ1 : θ < 1) :
    (iidLaw μ).real (inflationCutoff edges (fun _ => a) θ)ᶜ ≤
      disorderTailRemainder μ edges a θ := by
  apply (inflationCutoff_failure_le_card μ edges a θ).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply measureReal_mono ?_ (measure_ne_top μ _)
  intro x hx
  by_contra h
  exact (not_lt_of_ge (weight_inflation_le_half_of_abs_le ha hθ hθ1 (le_of_not_gt h))) hx

/-- General-disorder lower tail with the original normalized partition function,
exact graph mass at the actual edge variance, and the raw-disorder τ remainder. -/
theorem normalizedPartition_lower_tail_with_remainder (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (incidence : E → Finset V) (edges : Finset E) {a θ z : ℝ}
    (ha : 0 < a) (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z) :
    (iidLaw μ).real {J | SpinGlass.Partition.normalizedPartition incidence edges
        (fun e => a * J e) < z} ≤
      (∑ Γ ∈ SpinGlass.ConditionalSpinGlass.evenGraphs incidence edges,
        (secondMoment μ a / θ ^ 2) ^ Γ.card) *
        z ^ ((1 - Real.sqrt θ) / Real.sqrt θ) + disorderTailRemainder μ edges a θ := by
  exact (normalizedPartition_lower_tail_common_scale μ hμ incidence edges a hθ hθ1 hz).trans
    (add_le_add_right (inflationCutoff_failure_le_remainder μ edges ha hθ hθ1) _)

end SpinGlass.Disorder
