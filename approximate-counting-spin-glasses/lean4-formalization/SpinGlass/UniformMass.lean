import SpinGlass.UniformMassOverlap
import SpinGlass.FiniteTailMoment
import SpinGlass.UniformMassParameter
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The uniform auxiliary exponential moment and graphical mass

The exact entropy threshold, the finite-cube Chernoff estimate, the
repeated-index error, and the tail integration are all discharged by proved
lemmas. The constants agree with Lemma 4.2 and Proposition 4.3.
-/

noncomputable section
namespace SpinGlass.UniformMass
open Finset Real
open SpinGlass.Expansion SpinGlass.UniformMassEntropy SpinGlass.UniformMassOverlap

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Integrating the proved exact-entropy Chernoff bound. -/
theorem entropy_exponential_moment (hV : 0 < Fintype.card V) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    spinMean (fun σ : V → Bool => Real.exp (lam * ((Fintype.card V : ℝ) * entropy (overlap σ)))) ≤
      1 + 2 * lam / (1 - lam) := by
  have hweights : (∑ _σ : V → Bool, ((2 : ℝ)^Fintype.card V)⁻¹) = 1 := by
    simp [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  have htail : ∀ t : ℝ, 0 ≤ t →
      (∑ σ : V → Bool with t ≤ (Fintype.card V : ℝ) * entropy (overlap σ),
        ((2 : ℝ)^Fintype.card V)⁻¹) ≤ 2 * Real.exp (-t) := by
    intro t ht
    have h := entropy_tail (ι := V) hV ht
    rw [cubeProbability_eq_card] at h
    simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using h
  have h := SpinGlass.FiniteTailMoment.finite_exponential_moment
    (fun _σ : V → Bool => ((2 : ℝ)^Fintype.card V)⁻¹)
    (fun σ => (Fintype.card V : ℝ) * entropy (overlap σ))
    (fun _ => by positivity) hweights
    (fun σ => mul_nonneg (Nat.cast_nonneg _) (entropy_nonneg _)) htail hlam hlam1
  simpa only [spinMean, Finset.mul_sum] using h

/-- The explicit uniform constant, with the manuscript's precise `λ`. -/
def massConstant (p : ℕ) (v : ℝ) : ℝ :=
  Real.exp (v * delta p) * (1 + 2 * (v / thresholdSquared p) / (1 - v / thresholdSquared p))

/-- Lemma 4.2, for the actual distinct-index auxiliary interaction and the
full graphical second-moment threshold. No entropy or moment bound is assumed. -/
theorem auxiliary_exponential_moment {p : ℕ} (hp : 0 < p) (hpV : p ≤ Fintype.card V)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared p) :
    spinMean (fun σ : V → Bool => Real.exp (v * auxiliaryEnergy p σ)) ≤
      massConstant p v := by
  have hT : 0 < thresholdSquared p := lt_of_le_of_lt hv hvT
  have hV : 0 < Fintype.card V := lt_of_lt_of_le hp hpV
  have hlam : 0 ≤ v / thresholdSquared p := div_nonneg hv hT.le
  have hlam1 : v / thresholdSquared p < 1 := (div_lt_one hT).mpr hvT
  have hpoint : ∀ σ : V → Bool, Real.exp (v * auxiliaryEnergy p σ) ≤
      Real.exp (v * delta p) *
        Real.exp ((v / thresholdSquared p) * ((Fintype.card V : ℝ) * entropy (overlap σ))) := by
    intro σ
    have herror := (abs_le.mp (auxiliaryEnergy_error p hp hpV σ)).2
    have he := mul_le_mul_of_nonneg_left herror hv
    have hvar := scaled_overlap_power_le_entropy hp hv hvT (abs_overlap_le_one hV σ)
    have hvar' := mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf at he hvar' ⊢
    linarith
  have hm := mean_mono hpoint
  rw [spinMean_mul_left] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (entropy_exponential_moment hV hlam hlam1)
    (Real.exp_pos _).le)

/-- The uniform moment constant is at least one throughout its stated range. -/
theorem one_le_massConstant {p : ℕ} {v : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared p) :
    1 ≤ massConstant p v := by
  have hT : 0 < thresholdSquared p := lt_of_le_of_lt hv hvT
  have hlam : 0 ≤ v / thresholdSquared p := div_nonneg hv hT.le
  have hlam1 : v / thresholdSquared p < 1 := (div_lt_one hT).mpr hvT
  have hd : 0 ≤ delta p := by unfold delta; positivity
  have he : 1 ≤ Real.exp (v * delta p) := Real.one_le_exp_iff.mpr (mul_nonneg hv hd)
  have hfrac : 0 ≤ 2 * (v / thresholdSquared p) / (1 - v / thresholdSquared p) :=
    div_nonneg (mul_nonneg (by norm_num) hlam) (by linarith)
  exact one_le_mul_of_one_le_of_one_le he (by linarith)

/-- Proposition 4.3: a uniform bound on the actual positive even-graph mass.
The coefficient range and all analytic estimates are proved, not hypotheses. -/
theorem uniform_graphical_mass {p : ℕ} (hp : 0 < p) (hpV : p ≤ Fintype.card V)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared p) :
    (∑ Γ ∈ ((Finset.univ : Finset V).powersetCard p).powerset.filter (IsEven id),
      (v / (Fintype.card V : ℝ)^(p-1)) ^ Γ.card) ≤ massConstant p v := by
  have hz := SpinGlass.UniformMassParameter.mass_coefficient_range hp hpV hv hvT
  have h := SpinGlass.GraphicalMass.uniform_mass_le_exp_moment id
    ((Finset.univ : Finset V).powersetCard p) hz.1 hz.2.le
  have heq : (fun σ : V → Bool => Real.exp (v / (Fintype.card V : ℝ)^(p-1) *
      ∑ e ∈ (Finset.univ : Finset V).powersetCard p, edgeCharacter id σ e)) =
      (fun σ : V → Bool => Real.exp (v * auxiliaryEnergy p σ)) := by
    funext σ
    unfold auxiliaryEnergy
    congr 1
    ring
  rw [heq] at h
  exact h.trans (auxiliary_exponential_moment hp hpV hv hvT)

/-- A geometric tail for any finite family of edge sets, with every weight explicit. -/
theorem finite_geometric_tail {E : Type*} [DecidableEq E] (family : Finset (Finset E))
    {r q z : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hz : 0 ≤ z)
    (hrqz : r ≤ q * z) (m : ℕ) :
    (∑ Γ ∈ family.filter (fun Γ => m ≤ Γ.card), r ^ Γ.card) ≤
      q^m * ∑ Γ ∈ family, z ^ Γ.card := by
  calc
    _ ≤ ∑ Γ ∈ family.filter (fun Γ => m ≤ Γ.card), q^m * z^Γ.card := by
      apply Finset.sum_le_sum
      intro Γ hΓ
      have hcard := (Finset.mem_filter.mp hΓ).2
      calc
        r^Γ.card ≤ (q*z)^Γ.card := pow_le_pow_left₀ hr hrqz _
        _ = q^Γ.card * z^Γ.card := mul_pow _ _ _
        _ ≤ q^m * z^Γ.card := mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hq hq1 hcard) (pow_nonneg hz _)
    _ = q^m * ∑ Γ ∈ family.filter (fun Γ => m ≤ Γ.card), z^Γ.card := by rw [Finset.mul_sum]
    _ ≤ q^m * ∑ Γ ∈ family, z^Γ.card := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq _)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => pow_nonneg hz _)

/-- The exact integer geometric edge tail under inflation. -/
theorem graphical_edge_tail_nat {p : ℕ} (hp : 0 < p) (hpV : p ≤ Fintype.card V)
    {v r q : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared p)
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hrq : r ≤ q * (v / (Fintype.card V : ℝ)^(p-1))) (m : ℕ) :
    (∑ Γ ∈ (((Finset.univ : Finset V).powersetCard p).powerset.filter (IsEven id)).filter
      (fun Γ => m ≤ Γ.card), r^Γ.card) ≤ massConstant p v * q^m := by
  have hz : 0 ≤ v / (Fintype.card V : ℝ)^(p-1) := div_nonneg hv (by positivity)
  have h := finite_geometric_tail
    (((Finset.univ : Finset V).powersetCard p).powerset.filter (IsEven id))
    hr hq hq1 hz hrq m
  have hm := mul_le_mul_of_nonneg_left (uniform_graphical_mass hp hpV hv hvT) (pow_nonneg hq m)
  exact h.trans (by simpa only [mul_comm] using hm)

/-- Proposition 4.3's real-threshold version, including its floor refinement. -/
theorem graphical_edge_tail_real {p : ℕ} (hp : 0 < p) (hpV : p ≤ Fintype.card V)
    {v r q t : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared p)
    (hr : 0 ≤ r) (hq : 0 < q) (hq1 : q ≤ 1) (ht : 0 ≤ t)
    (hrq : r ≤ q * (v / (Fintype.card V : ℝ)^(p-1))) :
    (∑ Γ ∈ (((Finset.univ : Finset V).powersetCard p).powerset.filter (IsEven id)).filter
      (fun Γ => t < (Γ.card : ℝ)), r^Γ.card) ≤ massConstant p v * q^(Nat.floor t + 1) ∧
    massConstant p v * q^(Nat.floor t + 1) ≤ massConstant p v * q^t := by
  constructor
  · have heq : ∀ Γ : Finset (Finset V), (t < (Γ.card : ℝ)) ↔ Nat.floor t + 1 ≤ Γ.card := by
      intro Γ
      rw [← Nat.floor_lt ht]
      omega
    simp_rw [heq]
    exact graphical_edge_tail_nat hp hpV hv hvT hr hq.le hq1 hrq _
  · apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (one_le_massConstant hv hvT))
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hq hq1
    exact (by exact_mod_cast (Nat.lt_floor_add_one t).le)

end SpinGlass.UniformMass
