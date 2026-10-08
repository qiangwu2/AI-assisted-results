import SpinGlass.DisorderTailMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Tail consequences of finite and bounded disorder moments

The fourth-moment endpoint uses the vanishing truncated moment, not the weaker
constant bound obtained by ordinary Markov inequality. Real moment exponents
are retained throughout the polynomial-tail statement.
-/
noncomputable section
namespace SpinGlass.Disorder
open MeasureTheory Filter
open scoped Topology

/-- The moment integral on a moving absolute tail vanishes at infinity. -/
theorem abs_tail_integral_tendsto_zero (μ : Measure ℝ) {q : ℝ}
    (hint : Integrable (fun x : ℝ => |x|^q) μ) :
    Tendsto (fun t : ℝ => ∫ x in {x : ℝ | t< |x|}, |x|^q ∂μ) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone
    (μ:=μ) (f:=fun x : ℝ => |x|^q) (s:=fun t : ℝ => {x : ℝ | t< |x|})
    (fun t => measurableSet_lt measurable_const continuous_abs.measurable)
    (fun s t hst x hx => lt_of_le_of_lt hst hx) ⟨0,hint.integrableOn⟩
  have hempty : (⋂ t : ℝ, {x : ℝ | t< |x|})=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact lt_irrefl |x| ((Set.mem_iInter.mp hx) |x|)
  simpa only [hempty, Measure.restrict_empty, integral_zero_measure] using h

/-- The sharp tail-moment inequality retains the truncated moment on the right. -/
theorem rpow_mul_abs_tail_le_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : 0≤q) (hint : Integrable (fun x : ℝ => |x|^q) μ)
    {t : ℝ} (ht : 0≤t) :
    t^q * μ.real {x : ℝ | t< |x|} ≤ ∫ x in {x : ℝ | t< |x|}, |x|^q ∂μ := by
  have hs : MeasurableSet {x : ℝ | t< |x|} := measurableSet_lt measurable_const continuous_abs.measurable
  calc
    _ = ∫ _x in {x : ℝ | t< |x|}, t^q ∂μ := by rw [setIntegral_const]; simp [mul_comm]
    _ ≤ _ := integral_mono_ae (integrable_const _) hint.integrableOn
      ((ae_restrict_mem hs).mono (fun x hx => Real.rpow_le_rpow ht hx.le hq))

/-- Finite real q-th moment implies the strict little-o tail estimate t^q P(|J|>t)→0. -/
theorem rpow_mul_abs_tail_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : 0≤q) (hint : Integrable (fun x : ℝ => |x|^q) μ) :
    Tendsto (fun t : ℝ => t^q * μ.real {x : ℝ | t< |x|}) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (abs_tail_integral_tendsto_zero μ hint)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht _) MeasureTheory.measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact rpow_mul_abs_tail_le_integral μ hq hint ht

/-- Ordinary Markov inequality for a genuinely real absolute moment exponent. -/
theorem abs_tail_le_real_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : 0≤q) (hint : Integrable (fun x : ℝ => |x|^q) μ)
    {t : ℝ} (ht : 0<t) :
    μ.real {x : ℝ | t< |x|} ≤ (∫ x, |x|^q ∂μ)/t^q := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ:=μ) (f:=fun x : ℝ => |x|^q)
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _) hint (t^q)
  have hs : {x : ℝ | t< |x|} ⊆ {x : ℝ | t^q≤|x|^q} :=
    fun x hx => Real.rpow_le_rpow ht.le hx.le hq
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht _)).mpr
  calc
    μ.real {x : ℝ | t< |x|} * t^q ≤ μ.real {x : ℝ | t^q≤|x|^q} * t^q :=
      mul_le_mul_of_nonneg_right (measureReal_mono hs (measure_ne_top μ _))
        (Real.rpow_nonneg ht.le _)
    _ ≤ _ := by simpa only [mul_comm] using hm

/-- Scale of the raw tail in the pure p-spin model. -/
def tailPower (p : ℕ) : ℝ := ((p:ℝ)-1)/2

def tailCoefficient (B θ : ℝ) : ℝ := Real.artanh (θ/2)/B

theorem tailPower_pos {p : ℕ} (hp : 2≤p) : 0<tailPower p := by
  have h : (2:ℝ)≤p := by exact_mod_cast hp
  unfold tailPower
  linarith

theorem tailCoefficient_pos {B θ : ℝ} (hB : 0<B) (hθ : 0<θ) (hθ1 : θ<1) :
    0<tailCoefficient B θ :=
  div_pos (Real.artanh_pos ⟨by linarith,by linarith⟩) hB

/-- The threshold in τ_N is exactly c N^((p-1)/2), for the original scaling. -/
theorem pure_tail_threshold {N p : ℕ} (hN : 0<N) (hp : 1≤p) (B θ : ℝ) :
    Real.artanh (θ/2)/pureScale N p B = tailCoefficient B θ*(N:ℝ)^tailPower p := by
  have hNr : 0≤(N:ℝ) := Nat.cast_nonneg _
  have hs : Real.sqrt ((N:ℝ)^(p-1))=(N:ℝ)^tailPower p := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul hNr]
    congr 1
    simp only [tailPower, Nat.cast_sub hp, Nat.cast_one]
    ring
  rw [pureScale, div_div_eq_mul_div, hs, tailCoefficient]
  ring

theorem pure_tail_threshold_tendsto (p : ℕ) (hp : 2≤p) {B θ : ℝ}
    (hB : 0<B) (hθ : 0<θ) (hθ1 : θ<1) :
    Tendsto (fun N : ℕ => tailCoefficient B θ*(N:ℝ)^tailPower p) atTop atTop := by
  exact ((tendsto_rpow_atTop (tailPower_pos hp)).comp tendsto_natCast_atTop_atTop).const_mul_atTop
    (tailCoefficient_pos hB hθ hθ1)

/-- Exact p-edge count is at most N^p, independently of all asymptotic estimates. -/
theorem pure_remainder_le_scaled_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {N p : ℕ} (hN : 0<N) (hp : 1≤p) (B θ : ℝ) :
    disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p) (pureScale N p B) θ ≤
      (N:ℝ)^(p:ℝ)*μ.real {x : ℝ | tailCoefficient B θ*(N:ℝ)^tailPower p< |x|} := by
  rw [disorderTailRemainder, pure_tail_threshold hN hp]
  apply mul_le_mul_of_nonneg_right _ MeasureTheory.measureReal_nonneg
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Real.rpow_natCast]
  exact_mod_cast Nat.choose_le_pow N p

/-- Polynomially rescaled tails vanish even at the critical moment exponent. -/
theorem scaled_abs_tail_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q c d r : ℝ} (hq : 0≤q) (hint : Integrable (fun x : ℝ => |x|^q) μ)
    (hc : 0<c) (hd : 0<d) (hr : r≤d*q) :
    Tendsto (fun N : ℕ => (N:ℝ)^r * μ.real {x : ℝ | c*(N:ℝ)^d < |x|}) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => c*(N:ℝ)^d) atTop atTop :=
    Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop)
  have hz := ((rpow_mul_abs_tail_tendsto_zero μ hq hint).comp ht).const_mul (c^(-q))
  simp only [mul_zero] at hz
  apply squeeze_zero' _ _ hz
  · exact Filter.Eventually.of_forall (fun N =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) MeasureTheory.measureReal_nonneg)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
    have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
    have hcancel : c^(-q)*(c*(N:ℝ)^d)^q=(N:ℝ)^(d*q) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hN0 _), Real.rpow_neg hc.le,
        ← Real.rpow_mul hN0, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hc q)), one_mul]
    calc
      (N:ℝ)^r * μ.real {x : ℝ | c*(N:ℝ)^d < |x|} ≤
          (N:ℝ)^(d*q) * μ.real {x : ℝ | c*(N:ℝ)^d < |x|} :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 hr)
          MeasureTheory.measureReal_nonneg
      _ = c^(-q)*((c*(N:ℝ)^d)^q*μ.real {x : ℝ | c*(N:ℝ)^d < |x|}) := by
        rw [← mul_assoc,hcancel]

/-- General tail-rate endpoint for the actual pure-model remainder. This retains
real exponents and includes the equality case of the moment threshold. -/
theorem pure_remainder_weighted_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2≤p) {q b : ℝ} (hq : 0≤q)
    (hint : Integrable (fun x : ℝ => |x|^q) μ)
    {B θ : ℝ} (hB : 0<B) (hθ : 0<θ) (hθ1 : θ<1)
    (hm : (p:ℝ)+b≤tailPower p*q) :
    Tendsto (fun N : ℕ => (N:ℝ)^b *
      disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p)
        (pureScale N p B) θ) atTop (𝓝 0) := by
  have hz := scaled_abs_tail_tendsto_zero μ hq hint (tailCoefficient_pos hB hθ hθ1)
    (tailPower_pos hp) hm
  apply squeeze_zero' _ _ hz
  · exact Filter.Eventually.of_forall (fun N => by
      unfold disorderTailRemainder
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg (Nat.cast_nonneg _) MeasureTheory.measureReal_nonneg))
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have h := mul_le_mul_of_nonneg_left
      (pure_remainder_le_scaled_tail μ (by omega : 0<N) (by omega : 1≤p) B θ)
      (Real.rpow_nonneg hNr.le b)
    have he : (N:ℝ)^b * ((N:ℝ)^(p:ℝ) *
        μ.real {x : ℝ | tailCoefficient B θ*(N:ℝ)^tailPower p < |x|}) =
        (N:ℝ)^((p:ℝ)+b) * μ.real {x : ℝ | tailCoefficient B θ*(N:ℝ)^tailPower p < |x|} := by
      rw [Real.rpow_add hNr]
      ring
    exact h.trans_eq he

/-- Corollary 1.2's fourth-moment consequence, including the critical SK case p=2. -/
theorem pure_remainder_tendsto_zero_fourth (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2≤p) (h4 : Integrable (fun x : ℝ => |x|^4) μ)
    {B θ : ℝ} (hB : 0<B) (hθ : 0<θ) (hθ1 : θ<1) :
    Tendsto (fun N : ℕ =>
      disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p)
        (pureScale N p B) θ) atTop (𝓝 0) := by
  have h4r : Integrable (fun x : ℝ => |x|^(4:ℝ)) μ := by
    have he : (fun x : ℝ => |x|^(4:ℝ))=(fun x : ℝ => |x|^(4:ℕ)) :=
      funext (fun x => Real.rpow_natCast |x| 4)
    rw [he]
    exact h4
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hm : (p:ℝ)+0≤tailPower p*(4:ℝ) := by unfold tailPower; linarith
  simpa only [Real.rpow_zero,one_mul] using
    pure_remainder_weighted_tendsto_zero μ hp (by norm_num : (0:ℝ)≤4) h4r hB hθ hθ1 hm

/-- Corollary 1.3's real-moment hypothesis gives the required eventual polynomial
bound for exactly the τ_N occurring in the main theorem. -/
theorem pure_remainder_eventually_le_real_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2≤p) {m b : ℝ} (hb : 0<b)
    (hm : 2*((p:ℝ)+b)/((p:ℝ)-1)<m)
    (hint : Integrable (fun x : ℝ => |x|^m) μ)
    {B θ : ℝ} (hB : 0<B) (hθ : 0<θ) (hθ1 : θ<1) :
    ∀ᶠ N : ℕ in atTop,
      disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p)
        (pureScale N p B) θ ≤ (1/2:ℝ)*(N:ℝ)^(-b) := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hm' : 2*((p:ℝ)+b)<m*((p:ℝ)-1) := (div_lt_iff₀ hp1).mp hm
  have hmpos : 0<m := by
    have hpos : 0<2*((p:ℝ)+b) := by linarith
    by_contra h
    have hnon := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hp1.le
    linarith
  have hrate : (p:ℝ)+b≤tailPower p*m := by unfold tailPower; nlinarith
  have hz := pure_remainder_weighted_tendsto_zero μ hp hmpos.le hint hB hθ hθ1 hrate
  filter_upwards [hz.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    eventually_ge_atTop (1:ℕ)] with N hN hN1
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [Real.rpow_neg hNr.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hNr b)).mpr
  simpa only [mul_comm] using hN

/-- Bounded disorder makes the exact tail remainder identically zero eventually. -/
theorem pure_remainder_eventually_zero_of_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2≤p) {M : ℝ} (hbound : ∀ᵐ x : ℝ ∂μ, |x|≤M)
    {B θ : ℝ} (hB : 0<B) (hθ : 0<θ) (hθ1 : θ<1) :
    ∀ᶠ N : ℕ in atTop,
      disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p)
        (pureScale N p B) θ = 0 := by
  have ht := pure_tail_threshold_tendsto p hp hB hθ hθ1
  filter_upwards [ht.eventually (eventually_ge_atTop M), eventually_ge_atTop (1:ℕ)] with N hNM hN1
  rw [disorderTailRemainder, pure_tail_threshold (by omega : 0<N) (by omega : 1≤p)]
  have hzero : μ {x : ℝ | tailCoefficient B θ*(N:ℝ)^tailPower p < |x|}=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hbound] with x hx
    exact not_lt_of_ge (hx.trans hNM)
  rw [(measureReal_eq_zero_iff (measure_ne_top μ _)).mpr hzero, mul_zero]

end SpinGlass.Disorder
