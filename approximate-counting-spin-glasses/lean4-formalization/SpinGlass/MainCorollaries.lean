import SpinGlass.DisorderTailCorollaries
import SpinGlass.HigherOrderTotalCost
import SpinGlass.SKTotalTheorem
import SpinGlass.ConfidenceSchedules

/-!
# Moment consequences for the actual counting algorithms

The eventual quantifier precedes both requested temperature and accuracy. Thus
the sample-size threshold is uniform in these inputs, while each probability
still concerns one specified pair, as in Corollaries 1.2 and 1.3.
-/
noncomputable section
namespace SpinGlass.MainCorollaries
open MeasureTheory Filter
open scoped Topology
open SpinGlass.Disorder SpinGlass.DesignConstants SpinGlass.CountingReduction
open SpinGlass.ConfidenceSchedules

theorem theta_mem_Ioo {p : ℕ} {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    0 < theta p B ∧ theta p B < 1 := by
  have hp := (inflatedBeta_admissible hB hBT).1
  have hp0 := hB.trans hp
  exact ⟨div_pos hB hp0, (div_lt_one hp0).mpr hp⟩

theorem remainder_fourth (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2 ≤ p) (h4 : Integrable (fun x : ℝ => |x|^4) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    Tendsto (fun N : ℕ => remainder μ p N B) atTop (𝓝 0) := by
  have ht := theta_mem_Ioo hB hBT
  exact pure_remainder_tendsto_zero_fourth μ hp h4 hB ht.1 ht.2

theorem remainder_real_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2 ≤ p) {m b : ℝ} (hb : 0 < b)
    (hm : 2*((p:ℝ)+b)/((p:ℝ)-1) < m)
    (hint : Integrable (fun x : ℝ => |x|^m) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∀ᶠ N : ℕ in atTop, remainder μ p N B ≤ delta N b := by
  have ht := theta_mem_Ioo hB hBT
  exact pure_remainder_eventually_le_real_moment μ hp hb hm hint hB ht.1 ht.2

/-- For bounded disorder, the exact remainder in the main theorem vanishes. -/
theorem remainder_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2 ≤ p) {M : ℝ} (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ M)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∀ᶠ N : ℕ in atTop, remainder μ p N B = 0 := by
  have ht := theta_mem_Ioo hB hBT
  exact pure_remainder_eventually_zero_of_bounded μ hp hbound hB ht.1 ht.2

theorem delta_tendsto_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun N : ℕ => delta N b) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (N:ℝ)^(-b)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hb).comp tendsto_natCast_atTop_atTop
  simpa only [delta, mul_zero] using h.const_mul (1/2:ℝ)

theorem fourth_envelope (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2 ≤ p) (h4 : Integrable (fun x : ℝ => |x|^4) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    Tendsto (fun N : ℕ => remainder μ p N B + delta N 1) atTop (𝓝 0) := by
  simpa only [add_zero] using
    (remainder_fourth μ hp h4 hB hBT).add (delta_tendsto_zero (by norm_num : (0:ℝ) < 1))

/-- Failure event of the fully counted deterministic higher-order execution. -/
def higherFailure (μ : Measure ℝ) (p N : ℕ) (B beta epsilon d : ℝ) : ℝ :=
  (iidLaw μ).real {J : Finset (Fin N) → ℝ |
    epsilon < |(HigherOrderTotalCost.countedTotal p N B beta epsilon d J).value -
      targetLog p N beta J|}

/-- Failure of the actual total-cost SK output on its independent color/disorder
law. The validity test merely makes this failure functional total at unused
parameter values; all corollaries establish its admissible branch. -/
def skFailure (μ : Measure ℝ) (N : ℕ) (B beta epsilon d : ℝ) : ℝ := by
  classical
  exact if h : 0 < B ∧ B < betaThreshold 2 ∧ 0 < d then
    ((SKUniformAlgorithm.randomLaw N B (mseBudget 2 B epsilon d)).prod (iidLaw μ)).real
      {χJ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon d) ×
          (Finset (Fin N) → ℝ) |
        epsilon < |(SKTotalCost.countedTotal N B beta epsilon d h.1 h.2.1 h.2.2 χJ.1 χJ.2).value -
          targetLog 2 N beta χJ.2|}
    else 0

theorem sk_failure_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N : ℕ} (hN : 2 ≤ N) {B beta epsilon d : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < d) (hd1 : d < 1) :
    skFailure μ N B beta epsilon d ≤ remainder μ 2 N B + d := by
  classical
  simpa only [skFailure, dif_pos (show 0 < B ∧ B < betaThreshold 2 ∧ 0 < d from ⟨hB,hBT,hd⟩)] using
    SKTotalCost.counted_probability μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1

/-- Polynomial schedules retain a single fixed total-operation exponent for every
finite input array, including arbitrarily small positive requested accuracy. -/
theorem higher_scheduled_polynomial {p : ℕ} {B b : ℝ}
    (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, p ≤ N → ∀ beta epsilon : ℝ,
      0 < epsilon → epsilon < 1 → ∀ J : Finset (Fin N) → ℝ,
      ((HigherOrderTotalCost.countedTotal p N B beta epsilon (delta N b) J).operations : ℝ) ≤
        C*(N:ℝ)^C*epsilon^(-C) := by
  obtain ⟨k, hk, hcost⟩ := HigherOrderTotalCost.counted_polynomial hp hB hBT
  refine ⟨runtimeConstant k b, runtimeConstant_pos _ _, ?_⟩
  intro N hpN beta epsilon he he1 J
  have hN : 1 ≤ N := by omega
  exact (hcost N hpN beta epsilon (delta N b) he he1
    (delta_pos (by omega) b) (delta_lt_one hN hb) J).trans
      (runtime_substitution hN hk.le he he1.le b)

/-- Corollary 1.2, deterministic branch: a single confidence schedule works
uniformly for every specified temperature and accuracy. -/
theorem higher_fourth_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {p : ℕ} (hp : 3 ≤ p) (h4 : Integrable (fun x : ℝ => |x|^4) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ beta epsilon : ℝ,
      0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
      higherFailure μ p N B beta epsilon (delta N 1) ≤ eta := by
  filter_upwards [(fourth_envelope μ (by omega : 2 ≤ p) h4 hB hBT).eventually_le_const heta,
    eventually_ge_atTop p] with N htail hpN
  intro beta epsilon hbeta hbetaB he he1
  exact (HigherOrderTotalCost.counted_probability μ hμ hunit hp hpN hB hBT
    hbeta hbetaB he he1 (delta_pos (by omega) 1)
    (delta_lt_one (by omega) (by norm_num : (0:ℝ) ≤ 1))).trans htail

/-- Corollary 1.2, SK probability convention, uniform in both requested inputs. -/
theorem sk_fourth_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (h4 : Integrable (fun x : ℝ => |x|^4) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ beta epsilon : ℝ,
      0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
      skFailure μ N B beta epsilon (delta N 1) ≤ eta := by
  filter_upwards [(fourth_envelope μ (by omega : 2 ≤ 2) h4 hB hBT).eventually_le_const heta,
    eventually_ge_atTop (2:ℕ)] with N htail hN
  intro beta epsilon hbeta hbetaB he he1
  exact (sk_failure_bound μ hμ hunit hN hB hBT hbeta hbetaB he he1
    (delta_pos (by omega) 1) (delta_lt_one (by omega) (by norm_num : (0:ℝ) ≤ 1))).trans htail

/-- Corollary 1.3, deterministic branch, with the paper's genuinely real
moment exponent and a sample-size threshold independent of accuracy. -/
theorem higher_real_moment_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {p : ℕ} (hp : 3 ≤ p) {m b : ℝ} (hb : 0 < b)
    (hm : 2*((p:ℝ)+b)/((p:ℝ)-1) < m)
    (hint : Integrable (fun x : ℝ => |x|^m) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∀ᶠ N : ℕ in atTop, ∀ beta epsilon : ℝ,
      0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
      higherFailure μ p N B beta epsilon (delta N b) ≤ (N:ℝ)^(-b) := by
  filter_upwards [remainder_real_moment μ (by omega : 2 ≤ p) hb hm hint hB hBT,
    eventually_ge_atTop p] with N htail hpN
  intro beta epsilon hbeta hbetaB he he1
  have h := HigherOrderTotalCost.counted_probability μ hμ hunit hp hpN hB hBT
    hbeta hbetaB he he1 (delta_pos (N := N) (by omega) b)
      (delta_lt_one (N := N) (by omega) hb.le)
  exact h.trans (by dsimp [delta] at htail ⊢; linarith)

/-- Corollary 1.3 for SK, on its genuine joint color/disorder probability space. -/
theorem sk_real_moment_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {m b : ℝ} (hb : 0 < b) (hm : 2*((2:ℝ)+b)/((2:ℝ)-1) < m)
    (hint : Integrable (fun x : ℝ => |x|^m) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    ∀ᶠ N : ℕ in atTop, ∀ beta epsilon : ℝ,
      0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
      skFailure μ N B beta epsilon (delta N b) ≤ (N:ℝ)^(-b) := by
  filter_upwards [remainder_real_moment μ (by omega : 2 ≤ 2) hb hm hint hB hBT,
    eventually_ge_atTop (2:ℕ)] with N htail hN
  intro beta epsilon hbeta hbetaB he he1
  have h := sk_failure_bound μ hμ hunit hN hB hBT hbeta hbetaB he he1
    (delta_pos (N := N) (by omega) b) (delta_lt_one (N := N) (by omega) hb.le)
  exact h.trans (by dsimp [delta] at htail ⊢; linarith)

/-- The complete deterministic fourth-moment corollary, joining the uniform
probability statement with the actual algorithm's complete finite-index counter. -/
theorem higher_fourth_end_to_end (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {p : ℕ} (hp : 3 ≤ p) (h4 : Integrable (fun x : ℝ => |x|^4) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧
      (∀ N : ℕ, p ≤ N → ∀ beta epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∀ J : Finset (Fin N) → ℝ,
        ((HigherOrderTotalCost.countedTotal p N B beta epsilon (delta N 1) J).operations : ℝ) ≤
          C*(N:ℝ)^C*epsilon^(-C)) ∧
      (∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, ∀ beta epsilon : ℝ,
        0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
        higherFailure μ p N B beta epsilon (delta N 1) ≤ eta) := by
  obtain ⟨C,hC,hcost⟩ := higher_scheduled_polynomial hp hB hBT (by norm_num : (0:ℝ) ≤ 1)
  exact ⟨C,hC,hcost, fun _ heta => higher_fourth_uniform μ hμ hunit hp h4 hB hBT heta⟩

/-- The complete deterministic real-moment confidence corollary. -/
theorem higher_real_moment_end_to_end (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {p : ℕ} (hp : 3 ≤ p) {m b : ℝ} (hb : 0 < b)
    (hm : 2*((p:ℝ)+b)/((p:ℝ)-1) < m)
    (hint : Integrable (fun x : ℝ => |x|^m) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧
      (∀ N : ℕ, p ≤ N → ∀ beta epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∀ J : Finset (Fin N) → ℝ,
        ((HigherOrderTotalCost.countedTotal p N B beta epsilon (delta N b) J).operations : ℝ) ≤
          C*(N:ℝ)^C*epsilon^(-C)) ∧
      (∀ᶠ N : ℕ in atTop, ∀ beta epsilon : ℝ,
        0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
        higherFailure μ p N B beta epsilon (delta N b) ≤ (N:ℝ)^(-b)) := by
  obtain ⟨C,hC,hcost⟩ := higher_scheduled_polynomial hp hB hBT hb.le
  exact ⟨C,hC,hcost,higher_real_moment_uniform μ hμ hunit hp hb hm hint hB hBT⟩

/-- The randomized total schedule has a fixed polynomial after confidence
is specialized to delta_N=(1/2)N^-b. -/
theorem sk_scheduled_polynomial {B b : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N), ∀ beta epsilon : ℝ,
      0 < epsilon → epsilon < 1 →
      ∀ (χ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon (delta N b)))
        (J : Finset (Fin N) → ℝ),
      ((SKTotalCost.countedTotal N B beta epsilon (delta N b) hB hBT
        (delta_pos (by omega) b) χ J).operations : ℝ) ≤ C*(N:ℝ)^C*epsilon^(-C) := by
  obtain ⟨k,hk,hcost⟩ := SKTotalCost.counted_polynomial hB hBT
  refine ⟨runtimeConstant k b,runtimeConstant_pos _ _,?_⟩
  intro N hN beta epsilon he he1 χ J
  exact (hcost N hN beta epsilon (delta N b) he he1
    (delta_pos (by omega) b) (delta_lt_one (by omega) hb) χ J).trans
      (runtime_substitution (by omega) hk.le he he1.le b)

/-- Fourth-moment corollary for the actual sampled, cached, total-cost SK algorithm. -/
theorem sk_fourth_end_to_end (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (h4 : Integrable (fun x : ℝ => |x|^4) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N : ℕ) (hN : 2 ≤ N), ∀ beta epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∀ (χ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon (delta N 1)))
          (J : Finset (Fin N) → ℝ),
        ((SKTotalCost.countedTotal N B beta epsilon (delta N 1) hB hBT
          (delta_pos (by omega) 1) χ J).operations : ℝ) ≤ C*(N:ℝ)^C*epsilon^(-C)) ∧
      (∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, ∀ beta epsilon : ℝ,
        0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
        skFailure μ N B beta epsilon (delta N 1) ≤ eta) := by
  obtain ⟨C,hC,hcost⟩ := sk_scheduled_polynomial hB hBT (by norm_num : (0:ℝ) ≤ 1)
  exact ⟨C,hC,hcost,fun _ heta => sk_fourth_uniform μ hμ hunit h4 hB hBT heta⟩

/-- Real-moment confidence corollary for the actual randomized total schedule. -/
theorem sk_real_moment_end_to_end (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {m b : ℝ} (hb : 0 < b) (hm : 2*((2:ℝ)+b)/((2:ℝ)-1) < m)
    (hint : Integrable (fun x : ℝ => |x|^m) μ)
    {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N : ℕ) (hN : 2 ≤ N), ∀ beta epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∀ (χ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon (delta N b)))
          (J : Finset (Fin N) → ℝ),
        ((SKTotalCost.countedTotal N B beta epsilon (delta N b) hB hBT
          (delta_pos (by omega) b) χ J).operations : ℝ) ≤ C*(N:ℝ)^C*epsilon^(-C)) ∧
      (∀ᶠ N : ℕ in atTop, ∀ beta epsilon : ℝ,
        0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
        skFailure μ N B beta epsilon (delta N b) ≤ (N:ℝ)^(-b)) := by
  obtain ⟨C,hC,hcost⟩ := sk_scheduled_polynomial hB hBT hb.le
  exact ⟨C,hC,hcost,sk_real_moment_uniform μ hμ hunit hb hm hint hB hBT⟩

end SpinGlass.MainCorollaries
