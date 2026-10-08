import SpinGlass.DisorderUniform

/-!
# Restricted negative moments under arbitrary symmetric real disorder

Integrability of the restricted inverse power is proved, rather than assumed.
The finite sign estimate dominates each summand by a finite multiple of the
integrable inflated mass. This also works for arbitrary atoms at zero.
-/
noncomputable section
namespace SpinGlass.Disorder
open scoped BigOperators
open MeasureTheory SpinGlass.Expansion SpinGlass.ConditionalSpinGlass
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
theorem normalizedGraph_pos (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) (J : E → ℝ) : 0 < normalizedGraph incidence edges a J := by
  exact graphical_sum_pos incidence edges (fun e => weight (a e) (J e))
    (fun e _ => abs_weight_lt_one _ _)

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem inflationCutoff_signedArray_iff (edges : Finset E) (a : E → ℝ)
    (θ : ℝ) (J : E → ℝ) (η : E → Bool) :
    signedArray J η ∈ inflationCutoff edges a θ ↔ J ∈ inflationCutoff edges a θ := by
  simp only [inflationCutoff, Set.mem_setOf_eq, weight, signedArray, ← mul_assoc,
    tanh_mul_spinSign, abs_div, abs_mul, abs_spinSign, mul_one]

/-- Restricted inverse power on the actual inflation event. -/
def restrictedNegativeMomentIntegrand (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) (θ : ℝ) (J : E → ℝ) : ℝ := by
  classical
  exact if J ∈ inflationCutoff edges a θ then
    normalizedGraph incidence edges a J ^ (-((1 - Real.sqrt θ) / Real.sqrt θ)) else 0

/-- Sign-averaged restricted inverse power is bounded by the actual inflated mass. -/
theorem restricted_negative_signMean_le (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (J : E → ℝ) :
    spinMean (fun η => restrictedNegativeMomentIntegrand incidence edges a θ (signedArray J η)) ≤
      disorderInflatedMass incidence edges a θ J := by
  unfold restrictedNegativeMomentIntegrand
  by_cases hJ : J ∈ inflationCutoff edges a θ
  · have hη (η : E → Bool) : signedArray J η ∈ inflationCutoff edges a θ :=
      (inflationCutoff_signedArray_iff edges a θ J η).mpr hJ
    simp only [hη, ite_true, normalizedGraph_signedArray]
    exact fixed_magnitude_negative_moment incidence edges hθ hθ1
      (fun e => weight (a e) (J e)) hJ
  · have hη (η : E → Bool) : signedArray J η ∉ inflationCutoff edges a θ :=
      fun h => hJ ((inflationCutoff_signedArray_iff edges a θ J η).mp h)
    simp only [hη, ite_false, spinMean, Finset.sum_const_zero, mul_zero]
    exact inflatedMass_nonneg incidence edges θ _

/-- The restricted inverse power is integrable under the original disorder law;
this conclusion is obtained from finite sign averaging, not imposed as a premise. -/
theorem integrable_restrictedNegativeMoment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (incidence : E → Finset V) (edges : Finset E) (a : E → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    Integrable (restrictedNegativeMomentIntegrand incidence edges a θ) (iidLaw μ) := by
  classical
  let F := restrictedNegativeMomentIntegrand incidence edges a θ
  have hFnonneg (J : E → ℝ) : 0 ≤ F J := by
    dsimp [F, restrictedNegativeMomentIntegrand]
    split_ifs
    · exact Real.rpow_nonneg (normalizedGraph_pos incidence edges a J).le _
    · exact le_rfl
  have hFmeas : Measurable F :=
    ((continuous_normalizedGraph incidence edges a).measurable.pow_const _).ite
      (measurableSet_inflationCutoff edges a θ) measurable_const
  refine ((integrable_disorderInflatedMass μ incidence edges a θ).const_mul
    ((2 : ℝ) ^ Fintype.card E)).mono' hFmeas.aestronglyMeasurable ?_
  apply ae_of_all
  intro J
  rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg J)]
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (E → Bool))) (f := fun η => F (signedArray J η))
    (fun η _ => hFnonneg _) (Finset.mem_univ (fun _ : E => false))
  have hid : signedArray J (fun _ : E => false) = J := by
    funext e
    simp [signedArray, spinSign]
  rw [hid] at hsingle
  have hmean := mul_le_mul_of_nonneg_left
    (restricted_negative_signMean_le incidence edges a hθ hθ1 J)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Fintype.card E))
  have hscale : (2 : ℝ) ^ Fintype.card E * spinMean (fun η => F (signedArray J η)) =
      ∑ η : E → Bool, F (signedArray J η) := by
    rw [spinMean, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos (by norm_num) _)), one_mul]
  exact hsingle.trans (by simpa only [F, ← hscale] using hmean)

/-- The original-law restricted negative moment is bounded by the exact
averaged inflated even-graph mass, without an integrability assumption. -/
theorem normalizedGraph_restricted_negative_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (incidence : E → Finset V) (edges : Finset E) (a : E → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ J, restrictedNegativeMomentIntegrand incidence edges a θ J ∂iidLaw μ) ≤
      ∑ Γ ∈ evenGraphs incidence edges, ∏ e ∈ Γ, secondMoment μ (a e) / θ ^ 2 := by
  rw [← integral_signMean_eq_of_integrable μ hμ _
    (integrable_restrictedNegativeMoment μ incidence edges a hθ hθ1)]
  rw [← integral_disorderInflatedMass μ hμ incidence edges a θ]
  apply integral_mono_of_nonneg _ (integrable_disorderInflatedMass μ incidence edges a θ)
    (ae_of_all _ (restricted_negative_signMean_le incidence edges a hθ hθ1))
  apply ae_of_all
  intro J
  unfold spinMean
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro η hη
  unfold restrictedNegativeMomentIntegrand
  split_ifs
  · exact Real.rpow_nonneg (normalizedGraph_pos incidence edges a _).le _
  · exact le_rfl


/-- Proposition 4.5's restricted negative moment, with the actual uniform C+
and the full pure p-spin scaling, including β=0. The inflation event is at
least as large as the paper's raw-magnitude cutoff event. -/
theorem pure_p_spin_restricted_negative_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {β B βplus : ℝ} (hβ : 0 ≤ β) (hβB : β ≤ B) (hB : 0 < B)
    (hBplus : B < βplus)
    (hplusT : βplus ^ 2 < SpinGlass.UniformMassEntropy.thresholdSquared p) :
    (∫ J, restrictedNegativeMomentIntegrand
      (id : Finset (Fin N) → Finset (Fin N))
      ((Finset.univ : Finset (Fin N)).powersetCard p)
      (fun _ => pureScale N p β) (B / βplus) J ∂iidLaw μ) ≤
      SpinGlass.UniformMass.massConstant p (βplus ^ 2) := by
  have hN := lt_of_lt_of_le hp hpN
  have hplus := lt_trans hB hBplus
  have hθ : 0 < B / βplus := div_pos hB hplus
  have hθ1 : B / βplus < 1 := (div_lt_one hplus).mpr hBplus
  apply (normalizedGraph_restricted_negative_moment μ hμ id
    ((Finset.univ : Finset (Fin N)).powersetCard p) (fun _ => pureScale N p β) hθ hθ1).trans
  simp only [Finset.prod_const]
  have hvar : secondMoment μ (pureScale N p β) / (B / βplus) ^ 2 ≤
      βplus ^ 2 / (N : ℝ) ^ (p - 1) :=
    (div_le_div_of_nonneg_right (secondMoment_le_scale_sq μ hunit _) (sq_nonneg _)).trans
      (pureScale_inflation_bound hN hβ hβB hB hplus)
  apply (Finset.sum_le_sum (fun Γ hΓ => pow_le_pow_left₀
    (div_nonneg (secondMoment_nonneg μ _) (sq_nonneg _)) hvar Γ.card)).trans
  simpa only [evenGraphs, Fintype.card_fin] using
    (SpinGlass.UniformMass.uniform_graphical_mass (V := Fin N) hp (by simpa) (sq_nonneg _) hplusT)


/-- Restricting further to any measurable subevent of the inflation cutoff
preserves the proved inverse-moment bound. -/
theorem negative_moment_on_subevent (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (edges : Finset E)
    (a : E → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (S : Set (E → ℝ)) (hS : MeasurableSet S)
    (hsub : S ⊆ inflationCutoff edges a θ) :
    (∫ J in S, normalizedGraph incidence edges a J ^
      (-((1 - Real.sqrt θ) / Real.sqrt θ)) ∂iidLaw μ) ≤
      ∑ Γ ∈ evenGraphs incidence edges, ∏ e ∈ Γ, secondMoment μ (a e) / θ ^ 2 := by
  rw [← integral_indicator hS]
  apply (integral_mono_of_nonneg _
    (integrable_restrictedNegativeMoment μ incidence edges a hθ hθ1) _).trans
    (normalizedGraph_restricted_negative_moment μ hμ incidence edges a hθ hθ1)
  · apply ae_of_all
    intro J
    exact Set.indicator_nonneg (fun _ _ =>
      Real.rpow_nonneg (normalizedGraph_pos incidence edges a _).le _) J
  · apply ae_of_all
    intro J
    by_cases hJS : J ∈ S
    · rw [Set.indicator_of_mem hJS]
      simp only [restrictedNegativeMomentIntegrand, if_pos (hsub hJS), le_refl]
    · rw [Set.indicator_of_notMem hJS]
      unfold restrictedNegativeMomentIntegrand
      split_ifs
      · exact Real.rpow_nonneg (normalizedGraph_pos incidence edges a _).le _
      · exact le_rfl

/-- The raw cutoff in the manuscript, directly under the original law. -/
theorem raw_cutoff_restricted_negative_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (edges : Finset E)
    {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ J in {J : E → ℝ | ∀ e ∈ edges, |J e| ≤ Real.artanh (θ / 2) / a},
      SpinGlass.Partition.normalizedPartition incidence edges (fun e => a * J e) ^
      (-((1 - Real.sqrt θ) / Real.sqrt θ)) ∂iidLaw μ) ≤
      ∑ Γ ∈ evenGraphs incidence edges, (secondMoment μ a / θ ^ 2) ^ Γ.card := by
  have hS : MeasurableSet {J : E → ℝ | ∀ e ∈ edges, |J e| ≤ Real.artanh (θ / 2) / a} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun _ =>
      measurableSet_le (continuous_apply e).abs.measurable measurable_const
  have h := negative_moment_on_subevent μ hμ incidence edges (fun _ => a) hθ hθ1
    {J : E → ℝ | ∀ e ∈ edges, |J e| ≤ Real.artanh (θ / 2) / a} hS
    (fun J hJ e he => weight_inflation_le_half_of_abs_le ha hθ hθ1 (hJ e he))
  simpa only [normalizedGraph_eq_normalizedPartition, Finset.prod_const] using h

end SpinGlass.Disorder
