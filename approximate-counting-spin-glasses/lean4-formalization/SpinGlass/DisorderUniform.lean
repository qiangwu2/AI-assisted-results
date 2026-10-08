import SpinGlass.DisorderCutoff
import SpinGlass.UniformMass

/-!
# Uniform lower tails for the pure p-spin model

The exact original-disorder lower tail is combined with the proved uniform
graphical mass estimate. All distributional and analytic estimates are proved;
the hypotheses state the original probability law and scalar parameter ranges.
-/
noncomputable section
namespace SpinGlass.Disorder
open scoped BigOperators
open MeasureTheory SpinGlass.Expansion SpinGlass.ConditionalSpinGlass
open SpinGlass.UniformMass SpinGlass.UniformMassEntropy

/-- The uniformly bounded lower tail at any scaling whose inflated variance
is below the proved graphical threshold. -/
theorem pure_p_spin_lower_tail_of_scale_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {a θ z v : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z)
    (hv : 0 ≤ v) (hvT : v < thresholdSquared p)
    (hscale : a ^ 2 / θ ^ 2 ≤ v / (N : ℝ) ^ (p - 1)) :
    (iidLaw μ).real {J : Finset (Fin N) → ℝ |
      SpinGlass.Partition.normalizedPartition id
        ((Finset.univ : Finset (Fin N)).powersetCard p) (fun e => a * J e) < z} ≤
      massConstant p v * z ^ ((1 - Real.sqrt θ) / Real.sqrt θ) +
        disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p) a θ := by
  have hvar : secondMoment μ a / θ ^ 2 ≤ v / (N : ℝ) ^ (p - 1) :=
    (div_le_div_of_nonneg_right (secondMoment_le_scale_sq μ hunit a) (sq_nonneg θ)).trans hscale
  have hm : (∑ Γ ∈ evenGraphs (id : Finset (Fin N) → Finset (Fin N))
      ((Finset.univ : Finset (Fin N)).powersetCard p), (secondMoment μ a / θ ^ 2) ^ Γ.card) ≤ massConstant p v := by
    apply (Finset.sum_le_sum (fun Γ hΓ => pow_le_pow_left₀
      (div_nonneg (secondMoment_nonneg μ a) (sq_nonneg θ)) hvar Γ.card)).trans
    simpa only [Fintype.card_fin, evenGraphs] using
      (uniform_graphical_mass (V := Fin N) hp (by simpa) hv hvT)
  exact (normalizedPartition_lower_tail_with_remainder μ hμ id
    ((Finset.univ : Finset (Fin N)).powersetCard p) ha hθ hθ1 hz).trans
    (add_le_add (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hz.le _)) le_rfl)

/-- The physical coupling scale β/N^((p-1)/2), written with a square root. -/
def pureScale (N p : ℕ) (β : ℝ) : ℝ := β / Real.sqrt ((N : ℝ) ^ (p - 1))

theorem pureScale_pos {N p : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β) :
    0 < pureScale N p β := by
  exact div_pos hβ (Real.sqrt_pos.mpr (pow_pos (by exact_mod_cast hN) _))

theorem pureScale_sq {N p : ℕ} (_hN : 0 < N) (β : ℝ) :
    pureScale N p β ^ 2 = β ^ 2 / (N : ℝ) ^ (p - 1) := by
  rw [pureScale, div_pow, Real.sq_sqrt (pow_nonneg (Nat.cast_nonneg _) _)]

/-- The manuscript's fixed B, β+ inflation gives exactly the required
subcritical variance normalization, uniformly for β≤B. -/
theorem pureScale_inflation_bound {N p : ℕ} (hN : 0 < N)
    {β B βplus : ℝ} (hβ : 0 ≤ β) (hβB : β ≤ B) (hB : 0 < B) (hplus : 0 < βplus) :
    pureScale N p β ^ 2 / (B / βplus) ^ 2 ≤ βplus ^ 2 / (N : ℝ) ^ (p - 1) := by
  have hd : 0 < (N : ℝ) ^ (p - 1) := pow_pos (by exact_mod_cast hN) _
  have hr : 0 ≤ β / B := div_nonneg hβ hB.le
  have hr1 : β / B ≤ 1 := (div_le_one hB).mpr hβB
  calc
    _ = (β / B) ^ 2 * (βplus ^ 2 / (N : ℝ) ^ (p - 1)) := by
      rw [pureScale_sq hN]
      field_simp [hB.ne', hplus.ne', hd.ne']
    _ ≤ 1 * (βplus ^ 2 / (N : ℝ) ^ (p - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg (sq_nonneg _) hd.le)
      simpa using pow_le_pow_left₀ hr hr1 2
    _ = _ := one_mul _

/-- Proposition 4.5's C+ bound for the actual pure p-spin normalized partition
function at every positive β≤B<β+, where β+² is below the exact threshold. -/
theorem pure_p_spin_lower_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {β B βplus z : ℝ} (hβ : 0 < β) (hβB : β ≤ B)
    (hBplus : B < βplus) (hplusT : βplus ^ 2 < thresholdSquared p) (hz : 0 < z) :
    (iidLaw μ).real {J : Finset (Fin N) → ℝ |
      SpinGlass.Partition.normalizedPartition id
        ((Finset.univ : Finset (Fin N)).powersetCard p) (fun e => pureScale N p β * J e) < z} ≤
      massConstant p (βplus ^ 2) *
        z ^ ((1 - Real.sqrt (B / βplus)) / Real.sqrt (B / βplus)) +
      disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p) (pureScale N p β) (B / βplus) := by
  have hN := lt_of_lt_of_le hp hpN
  have hB := lt_of_lt_of_le hβ hβB
  have hplus := lt_trans hB hBplus
  exact pure_p_spin_lower_tail_of_scale_bound μ hμ hunit hp hpN
    (pureScale_pos hN hβ) (div_pos hB hplus) ((div_lt_one hplus).mpr hBplus) hz
    (sq_nonneg _) hplusT (pureScale_inflation_bound hN hβ.le hβB hB hplus)


/-- The raw-disorder remainder is monotone in the positive coupling scale. -/
theorem disorderTailRemainder_mono {E : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (edges : Finset E) {a b θ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hθ : 0 ≤ θ) :
    disorderTailRemainder μ edges a θ ≤ disorderTailRemainder μ edges b θ := by
  unfold disorderTailRemainder
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply measureReal_mono ?_ (measure_ne_top μ _)
  intro x hx
  exact lt_of_le_of_lt
    (div_le_div_of_nonneg_left (Real.artanh_nonneg (by linarith)) ha hab) hx

/-- Uniformity in β includes the zero-temperature endpoint. The τ remainder
is fixed at B, so neither C+ nor τ varies with the chosen β∈[0,B]. -/
theorem pure_p_spin_lower_tail_uniform_temperature (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {β B βplus z : ℝ} (hβ : 0 ≤ β) (hβB : β ≤ B) (hB : 0 < B)
    (hBplus : B < βplus) (hplusT : βplus ^ 2 < thresholdSquared p)
    (hz : 0 < z) (hz1 : z ≤ 1) :
    (iidLaw μ).real {J : Finset (Fin N) → ℝ |
      SpinGlass.Partition.normalizedPartition id
        ((Finset.univ : Finset (Fin N)).powersetCard p) (fun e => pureScale N p β * J e) < z} ≤
      massConstant p (βplus ^ 2) *
        z ^ ((1 - Real.sqrt (B / βplus)) / Real.sqrt (B / βplus)) +
      disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p)
        (pureScale N p B) (B / βplus) := by
  have hN := lt_of_lt_of_le hp hpN
  have hplus := lt_trans hB hBplus
  by_cases hβ0 : β = 0
  · have hzero (J : Finset (Fin N) → ℝ) :
        SpinGlass.Partition.normalizedPartition id
          ((Finset.univ : Finset (Fin N)).powersetCard p) (fun e => pureScale N p β * J e) = 1 := by
      simp [hβ0, pureScale, SpinGlass.Partition.normalizedPartition,
        SpinGlass.Partition.partitionFunction, SpinGlass.Partition.prefactor]
    simp only [hzero, show ¬(1 : ℝ) < z from not_lt_of_ge hz1, Set.setOf_false, measureReal_empty]
    apply add_nonneg
    · exact mul_nonneg (le_trans zero_le_one (one_le_massConstant (sq_nonneg _) hplusT))
        (Real.rpow_nonneg hz.le _)
    · exact mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
  · have hβpos := lt_of_le_of_ne hβ (Ne.symm hβ0)
    have hscale : pureScale N p β ≤ pureScale N p B :=
      div_le_div_of_nonneg_right hβB (Real.sqrt_nonneg _)
    exact (pure_p_spin_lower_tail μ hμ hunit hp hpN hβpos hβB hBplus hplusT hz).trans
      (add_le_add le_rfl (disorderTailRemainder_mono μ _ (pureScale_pos hN hβpos) hscale
        (div_nonneg hB.le hplus.le)))

end SpinGlass.Disorder
