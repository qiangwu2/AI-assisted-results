import SpinGlass.DisorderSigns
import SpinGlass.ConditionalSpinGlass

/-!
# Lower tails under the original symmetric real disorder

The finite-sign theorem is integrated against the original iid real disorder.
The cutoff failure probability and the inflated graph mass remain explicit;
neither is assumed to be bounded by the desired final constants.
-/
noncomputable section
namespace SpinGlass.Disorder
open scoped BigOperators
open MeasureTheory SpinGlass.Expansion SpinGlass.ConditionalSpinGlass

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The actual normalized partition function in graphical coordinates. -/
def normalizedGraph (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) (J : E → ℝ) : ℝ :=
  ∑ Γ ∈ evenGraphs incidence edges, monomial a Γ J

omit [Fintype E] [DecidableEq E] in
theorem normalizedGraph_eq_normalizedPartition (incidence : E → Finset V)
    (edges : Finset E) (a : E → ℝ) (J : E → ℝ) :
    normalizedGraph incidence edges a J =
      SpinGlass.Partition.normalizedPartition incidence edges (fun e => a e * J e) := by
  rw [SpinGlass.Partition.normalizedPartition_eq_even_sum]
  rfl

omit [Fintype E] [DecidableEq E] in
theorem continuous_normalizedGraph (incidence : E → Finset V)
    (edges : Finset E) (a : E → ℝ) : Continuous (normalizedGraph incidence edges a) := by
  exact continuous_finsetSum _ fun Γ _ => continuous_monomial a Γ

omit [Fintype E] [DecidableEq E] in
theorem normalizedGraph_signedArray (incidence : E → Finset V)
    (edges : Finset E) (a : E → ℝ) (J : E → ℝ) (η : E → Bool) :
    normalizedGraph incidence edges a (signedArray J η) =
      graphPolynomial incidence edges (fun e => weight (a e) (J e)) η := by
  unfold normalizedGraph graphPolynomial monomial weight signedArray
  simp_rw [← mul_assoc, tanh_mul_spinSign, Finset.prod_mul_distrib]
  rfl

/-- The measurable event on which every inflated edge weight is at most one half. -/
def inflationCutoff (edges : Finset E) (a : E → ℝ) (θ : ℝ) : Set (E → ℝ) :=
  {J | ∀ e ∈ edges, |weight (a e) (J e) / θ| ≤ 1 / 2}

omit [DecidableEq E] in
theorem measurableSet_inflationCutoff (edges : Finset E) (a : E → ℝ) (θ : ℝ) :
    MeasurableSet (inflationCutoff edges a θ) := by
  unfold inflationCutoff
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro he
  exact measurableSet_le
    ((((continuous_weight (a e)).comp (continuous_apply e)).div_const θ).abs.measurable)
    measurable_const

/-- The inflated mass evaluated on the original random weight array. -/
def disorderInflatedMass (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) (θ : ℝ) (J : E → ℝ) : ℝ :=
  inflatedMass incidence edges θ (fun e => weight (a e) (J e))

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem integrable_monomial_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : E → ℝ) (Γ : Finset E) :
    Integrable (fun J => monomial a Γ J ^ 2) (iidLaw μ) := by
  simpa only [sq] using integrable_monomial_mul μ a Γ Γ

omit [DecidableEq E] in
/-- Each inflated squared monomial is an integrable bounded function; the
bound may depend on the finite graph and inflation parameter. -/
theorem integrable_disorderInflatedMass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (incidence : E → Finset V) (edges : Finset E) (a : E → ℝ) (θ : ℝ) :
    Integrable (disorderInflatedMass incidence edges a θ) (iidLaw μ) := by
  unfold disorderInflatedMass inflatedMass
  apply integrable_finsetSum
  intro Γ hΓ
  have heq : (fun J : E → ℝ => ∏ e ∈ Γ, (weight (a e) (J e) / θ) ^ 2) =
      (fun J => monomial a Γ J ^ 2 / (θ ^ Γ.card) ^ 2) := by
    funext J
    simp only [monomial, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
      Finset.prod_const, ← pow_mul]
  rw [heq]
  exact (integrable_monomial_sq μ a Γ).div_const ((θ ^ Γ.card) ^ 2)

/-- The averaged inflated mass is exactly the graphical mass at the true
single-edge variances divided by the inflation parameter squared. -/
theorem integral_disorderInflatedMass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) (θ : ℝ) :
    (∫ J, disorderInflatedMass incidence edges a θ J ∂iidLaw μ) =
      ∑ Γ ∈ evenGraphs incidence edges, ∏ e ∈ Γ, secondMoment μ (a e) / θ ^ 2 := by
  have hint (Γ : Finset E) : Integrable
      (fun J => ∏ e ∈ Γ, (weight (a e) (J e) / θ) ^ 2) (iidLaw μ) := by
    convert (integrable_monomial_sq μ a Γ).div_const ((θ ^ Γ.card) ^ 2) using 1
    funext J
    simp only [monomial, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
    Finset.prod_const, ← pow_mul]
  unfold disorderInflatedMass inflatedMass
  rw [integral_finsetSum _ (fun Γ _ => hint Γ)]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  calc
    _ = (∫ J, monomial a Γ J ^ 2 ∂iidLaw μ) / (θ ^ Γ.card) ^ 2 := by
      rw [← integral_div]
      congr 1
      funext J
      simp only [monomial, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
    Finset.prod_const, ← pow_mul]
    _ = (∏ e ∈ Γ, secondMoment μ (a e)) / (θ ^ Γ.card) ^ 2 := by
      have h := monomial_orthogonality μ hμ a Γ Γ
      simpa only [ite_true, ← sq] using congrArg (fun t => t / (θ ^ Γ.card) ^ 2) h
    _ = _ := by simp only [Finset.prod_div_distrib, Finset.prod_const, ← pow_mul, Nat.mul_comm]

/-- A finite uniform cube average of an event indicator is its counting proportion. -/
theorem spinMean_event_indicator (P : (E → Bool) → Prop) [DecidablePred P] :
    spinMean (fun η => if P η then (1 : ℝ) else 0) =
      ((Finset.univ.filter P).card : ℝ) / (2 : ℝ) ^ Fintype.card E := by
  rw [spinMean, Finset.sum_boole, div_eq_mul_inv, mul_comm]

omit [Fintype V] [DecidableEq V] in
theorem spinMean_event_indicator_le_one (P : (E → Bool) → Prop) [DecidablePred P] :
    spinMean (fun η => if P η then (1 : ℝ) else 0) ≤ 1 := by
  rw [spinMean_event_indicator]
  apply (div_le_one (by positivity)).2
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (E → Bool))) P
  have hnat : (Finset.univ.filter P).card ≤ 2 ^ Fintype.card E := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] using h
  exact_mod_cast hnat

/-- The actual disorder lower-tail probability, with its exact averaged
inflated graphical mass and explicit cutoff failure probability. -/
theorem normalizedGraph_lower_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) {θ z : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z) :
    (iidLaw μ).real {J | normalizedGraph incidence edges a J < z} ≤
      (∑ Γ ∈ evenGraphs incidence edges, ∏ e ∈ Γ, secondMoment μ (a e) / θ ^ 2) *
        z ^ ((1 - Real.sqrt θ) / Real.sqrt θ) +
      (iidLaw μ).real (inflationCutoff edges a θ)ᶜ := by
  classical
  let F : (E → ℝ) → ℝ := fun J => if normalizedGraph incidence edges a J < z then 1 else 0
  let B : (E → ℝ) → ℝ := fun J => if J ∈ inflationCutoff edges a θ then 0 else 1
  let s : ℝ := (1 - Real.sqrt θ) / Real.sqrt θ
  have hevent : MeasurableSet {J | normalizedGraph incidence edges a J < z} :=
    measurableSet_lt (continuous_normalizedGraph incidence edges a).measurable measurable_const
  have hF : Measurable F := measurable_const.ite hevent measurable_const
  have hFbound : ∀ J, ‖F J‖ ≤ 1 := by intro J; simp only [F]; split_ifs <;> norm_num
  have hBind : B = (inflationCutoff edges a θ)ᶜ.indicator (1 : (E → ℝ) → ℝ) := by
    funext J
    by_cases hJ : J ∈ inflationCutoff edges a θ <;> simp [B, Set.indicator, hJ]
  have hB : Integrable B (iidLaw μ) := by
    have h := (integrable_const (1 : ℝ) : Integrable (fun _ : E → ℝ => (1 : ℝ)) (iidLaw μ)).indicator
      (measurableSet_inflationCutoff edges a θ).compl
    rw [hBind]
    exact h
  have hpoint (J : E → ℝ) : spinMean (fun η => F (signedArray J η)) ≤
      disorderInflatedMass incidence edges a θ J * z ^ s + B J := by
    simp only [F, normalizedGraph_signedArray]
    by_cases hJ : J ∈ inflationCutoff edges a θ
    · have h := fixed_magnitude_lower_tail incidence edges hθ hθ1 hz
        (fun e => weight (a e) (J e)) hJ
      rw [spinMean_event_indicator]
      simpa only [disorderInflatedMass, s, B, if_pos hJ, add_zero] using h
    · have h := spinMean_event_indicator_le_one
        (fun η => graphPolynomial incidence edges (fun e => weight (a e) (J e)) η < z)
      have hm := inflatedMass_nonneg incidence edges θ (fun e => weight (a e) (J e))
      have hzpow := Real.rpow_nonneg hz.le s
      simp only [B, if_neg hJ]
      exact h.trans (by dsimp [disorderInflatedMass]; nlinarith)
  have hnonneg : ∀ J, 0 ≤ spinMean (fun η => F (signedArray J η)) := by
    intro J
    unfold spinMean
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun η _ => by dsimp [F]; split_ifs <;> norm_num
  calc
    (iidLaw μ).real {J | normalizedGraph incidence edges a J < z} =
        ∫ J, F J ∂iidLaw μ := by
      symm
      simpa [F, Set.indicator] using integral_indicator_one (μ := iidLaw μ) hevent
    _ = ∫ J, spinMean (fun η => F (signedArray J η)) ∂iidLaw μ :=
      (integral_signMean_eq μ hμ F hF 1 hFbound).symm
    _ ≤ ∫ J, (disorderInflatedMass incidence edges a θ J * z ^ s + B J) ∂iidLaw μ :=
      integral_mono_of_nonneg (ae_of_all _ hnonneg)
        (((integrable_disorderInflatedMass μ incidence edges a θ).mul_const _).add hB)
        (ae_of_all _ hpoint)
    _ = _ := by
      rw [integral_add ((integrable_disorderInflatedMass μ incidence edges a θ).mul_const _) hB,
        integral_mul_const, integral_disorderInflatedMass μ hμ]
      congr 1
      rw [hBind]
      exact integral_indicator_one (μ := iidLaw μ) (measurableSet_inflationCutoff edges a θ).compl


/-- Direct statement for the normalized exponential partition function in the
paper, with the complete original real-disorder probability measure. -/
theorem normalizedPartition_lower_tail_iid (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) {θ z : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z) :
    (iidLaw μ).real {J | SpinGlass.Partition.normalizedPartition incidence edges
        (fun e => a e * J e) < z} ≤
      (∑ Γ ∈ evenGraphs incidence edges, ∏ e ∈ Γ, secondMoment μ (a e) / θ ^ 2) *
        z ^ ((1 - Real.sqrt θ) / Real.sqrt θ) +
      (iidLaw μ).real (inflationCutoff edges a θ)ᶜ := by
  simpa only [normalizedGraph_eq_normalizedPartition] using
    normalizedGraph_lower_tail μ hμ incidence edges a hθ hθ1 hz

/-- For common scaling, the graph mass is the power of the actual single-edge
second moment for each graph, as in the manuscript. -/
theorem normalizedPartition_lower_tail_common_scale (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (incidence : E → Finset V) (edges : Finset E) (a : ℝ)
    {θ z : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z) :
    (iidLaw μ).real {J | SpinGlass.Partition.normalizedPartition incidence edges
        (fun e => a * J e) < z} ≤
      (∑ Γ ∈ evenGraphs incidence edges, (secondMoment μ a / θ ^ 2) ^ Γ.card) *
        z ^ ((1 - Real.sqrt θ) / Real.sqrt θ) +
      (iidLaw μ).real (inflationCutoff edges (fun _ => a) θ)ᶜ := by
  simpa only [Finset.prod_const] using
    normalizedPartition_lower_tail_iid μ hμ incidence edges (fun _ => a) hθ hθ1 hz


omit [DecidableEq E] in
/-- Union bound for the actual failed inflation cutoff, using the one-edge
law exactly and making no moment or tail assumption. -/
theorem inflationCutoff_failure_le_sum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (edges : Finset E) (a : E → ℝ) (θ : ℝ) :
    (iidLaw μ).real (inflationCutoff edges a θ)ᶜ ≤
      ∑ e ∈ edges, μ.real {x : ℝ | 1 / 2 < |weight (a e) x / θ|} := by
  classical
  have heq : (inflationCutoff edges a θ)ᶜ =
      ⋃ e ∈ edges, {J : E → ℝ | 1 / 2 < |weight (a e) (J e) / θ|} := by
    ext J
    simp [inflationCutoff, not_forall, not_le]
  rw [heq]
  apply (measureReal_biUnion_finset_le edges _).trans
  apply Finset.sum_le_sum
  intro e he
  have hp := measurePreserving_eval (μ := fun _ : E => μ) e
  have hm : MeasurableSet {x : ℝ | 1 / 2 < |weight (a e) x / θ|} :=
    measurableSet_lt measurable_const ((continuous_weight (a e)).div_const θ).abs.measurable
  have h := map_measureReal_apply (μ := iidLaw μ) (measurable_pi_apply e) hm
  rw [show (iidLaw μ).map (Function.eval e) = μ from hp.map_eq] at h
  exact h.symm.le

/-- For iid edges with common scaling, the cutoff failure is at most the
number of interactions times the exact one-edge cutoff failure probability. -/
theorem inflationCutoff_failure_le_card (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (edges : Finset E) (a θ : ℝ) :
    (iidLaw μ).real (inflationCutoff edges (fun _ => a) θ)ᶜ ≤
      edges.card * μ.real {x : ℝ | 1 / 2 < |weight a x / θ|} := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    inflationCutoff_failure_le_sum μ edges (fun _ => a) θ

end SpinGlass.Disorder
