import SpinGlass.DisorderUniform

/-! # Explicit moment bounds for the raw-disorder remainder -/
noncomputable section
namespace SpinGlass.Disorder
open MeasureTheory

/-- Markov's bound for any natural absolute moment of the original disorder. -/
theorem abs_tail_le_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q : ℕ) (hint : Integrable (fun x : ℝ => |x| ^ q) μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {x : ℝ | t < |x|} ≤ (∫ x : ℝ, |x| ^ q ∂μ) / t ^ q := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun x : ℝ => |x| ^ q)
    (ae_of_all _ fun x => pow_nonneg (abs_nonneg x) q) hint (t ^ q)
  have hsubset : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ^ q ≤ |x| ^ q} := by
    intro x hx
    exact pow_le_pow_left₀ ht.le hx.le q
  have hmeas := measureReal_mono (μ := μ) hsubset (measure_ne_top μ _)
  apply (le_div_iff₀ (pow_pos ht q)).mpr
  calc
    μ.real {x : ℝ | t < |x|} * t ^ q ≤
        μ.real {x : ℝ | t ^ q ≤ |x| ^ q} * t ^ q :=
      mul_le_mul_of_nonneg_right hmeas (pow_nonneg ht.le q)
    _ ≤ ∫ x : ℝ, |x| ^ q ∂μ := by simpa only [mul_comm] using hmarkov

/-- A finite q-th moment quantitatively controls exactly the τ remainder
appearing in the proved lower-tail bound. -/
theorem disorderTailRemainder_le_moment {E : Type*} (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (edges : Finset E) (q : ℕ)
    (hint : Integrable (fun x : ℝ => |x| ^ q) μ)
    {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hθ1 : θ < 1) :
    disorderTailRemainder μ edges a θ ≤
      edges.card * (∫ x : ℝ, |x| ^ q ∂μ) / (Real.artanh (θ / 2) / a) ^ q := by
  unfold disorderTailRemainder
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact abs_tail_le_moment μ q hint
    (div_pos (Real.artanh_pos ⟨by linarith, by linarith⟩) ha)

/-- The explicit even-moment rate before replacing the interaction count
by a polynomial: N^(-(p-1)k) times the exact number of p-spin interactions. -/
theorem pure_remainder_le_even_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {N p : ℕ} (hN : 0 < N) (k : ℕ)
    (hint : Integrable (fun x : ℝ => |x| ^ (2 * k)) μ)
    {B θ : ℝ} (hB : 0 < B) (hθ : 0 < θ) (hθ1 : θ < 1) :
    disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p)
      (pureScale N p B) θ ≤
      ((Finset.univ : Finset (Fin N)).powersetCard p).card *
        (∫ x : ℝ, |x| ^ (2 * k) ∂μ) *
        (B / Real.artanh (θ / 2)) ^ (2 * k) / (N : ℝ) ^ ((p - 1) * k) := by
  have hd : 0 < (N : ℝ) ^ (p - 1) := pow_pos (by exact_mod_cast hN) _
  have hc : 0 < Real.artanh (θ / 2) := Real.artanh_pos ⟨by linarith, by linarith⟩
  apply (disorderTailRemainder_le_moment μ _ (2 * k) hint (pureScale_pos hN hB) hθ hθ1).trans_eq
  rw [pureScale, div_div_eq_mul_div]
  have hsqrt : Real.sqrt ((N : ℝ) ^ (p - 1)) ^ (2 * k) =
      ((N : ℝ) ^ (p - 1)) ^ k := by rw [pow_mul, Real.sq_sqrt hd.le]
  rw [div_pow, mul_pow, hsqrt, div_pow, ← pow_mul]
  field_simp

end SpinGlass.Disorder
