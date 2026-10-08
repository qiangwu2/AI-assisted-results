import SpinGlass.GraphicalMass
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The exact overlap entropy and finite-cube Chernoff estimates

The entropy below is the manuscript's Ising rate function, not its quadratic
relaxation. All averages are over the actual finite uniform sign cube.
-/

noncomputable section
namespace SpinGlass.UniformMassEntropy
open Finset Real
open SpinGlass.Expansion

/-- The exact Ising overlap entropy, continuously defined at the endpoints. -/
def entropy (x : ℝ) : ℝ :=
  ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2

@[simp] theorem entropy_zero : entropy 0 = 0 := by simp [entropy]
@[simp] theorem entropy_neg (x : ℝ) : entropy (-x) = entropy x := by
  simp only [entropy, sub_neg_eq_add]
  congr 1 <;> ring
@[simp] theorem entropy_one : entropy 1 = Real.log 2 := by norm_num [entropy]

/-- Binary entropy and the manuscript's overlap entropy are complementary. -/
theorem entropy_eq_log_two_sub_binEntropy (x : ℝ) :
    entropy x = Real.log 2 - Real.binEntropy ((1 + x) / 2) := by
  by_cases hx1 : x = 1
  · subst x
    norm_num [entropy]
  by_cases hx2 : x = -1
  · subst x
    norm_num [entropy]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold entropy Real.negMulLog
  have heq : 1 - (1 + x) / 2 = (1 - x) / 2 := by ring
  rw [heq]
  rw [Real.log_div (by intro h; apply hx2; linarith : 1 + x ≠ 0) (by norm_num),
    Real.log_div (by intro h; apply hx1; linarith : 1 - x ≠ 0) (by norm_num)]
  ring

/-- Nonnegativity of the exact entropy holds including the endpoints. -/
theorem entropy_nonneg (x : ℝ) : 0 ≤ entropy x := by
  rw [entropy_eq_log_two_sub_binEntropy]
  exact sub_nonneg.mpr Real.binEntropy_le_log_two

/-- Positive overlap has strictly positive exact entropy. -/
theorem entropy_pos {x : ℝ} (hx : x ≠ 0) : 0 < entropy x := by
  rw [entropy_eq_log_two_sub_binEntropy]
  apply sub_pos.mpr
  apply Real.binEntropy_lt_log_two.mpr
  intro heq
  norm_num at heq
  exact hx (by linarith)

/-- The exact entropy is increasing in the absolute overlap. -/
theorem entropy_strictMonoOn : StrictMonoOn entropy (Set.Icc 0 1) := by
  intro x hx y hy hxy
  rw [entropy_eq_log_two_sub_binEntropy, entropy_eq_log_two_sub_binEntropy]
  have hx' : (1 + x) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := by constructor <;> norm_num at * <;> linarith
  have hy' : (1 + y) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := by constructor <;> norm_num at * <;> linarith
  have h := Real.binEntropy_strictAntiOn hx' hy' (by linarith)
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual sum and mean of the independent overlap signs. -/
def signSum (σ : ι → Bool) : ℝ := ∑ i, spinSign (σ i)
def overlap (σ : ι → Bool) : ℝ := signSum σ / Fintype.card ι

theorem abs_signSum_le_card (σ : ι → Bool) :
    |signSum σ| ≤ Fintype.card ι := by
  calc
    |signSum σ| ≤ ∑ i, |spinSign (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = Fintype.card ι := by simp

theorem abs_overlap_le_one (hι : 0 < Fintype.card ι) (σ : ι → Bool) :
    |overlap σ| ≤ 1 := by
  unfold overlap
  rw [abs_div, Nat.abs_cast]
  exact (div_le_one (Nat.cast_pos.mpr hι)).mpr (abs_signSum_le_card σ)

/-- The exact moment generating function factors into single-spin coshes. -/
theorem signSum_mgf (t : ℝ) :
    spinMean (fun σ : ι → Bool => Real.exp (t * signSum σ)) =
      Real.cosh t ^ Fintype.card ι := by
  unfold signSum spinMean
  simp_rw [show ∀ σ : ι → Bool, t * ∑ i, spinSign (σ i) = ∑ i, t * spinSign (σ i) from fun _ => Finset.mul_sum .., Real.exp_sum]
  rw [← Fintype.prod_sum (fun (_i : ι) (b : Bool) => Real.exp (t * spinSign b))]
  have hbit : (∑ b : Bool, Real.exp (t * spinSign b)) = 2 * Real.cosh t := by
    simp [spinSign, Real.cosh_eq]
    ring
  simp only [hbit, Finset.prod_const, Finset.card_univ, mul_pow]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]

/-- A normalized positive tilt. It is defined without any probabilistic axioms. -/
def tiltedWeight (x : ℝ) (σ : ι → Bool) : ℝ :=
  ∏ i, (1 + x * spinSign (σ i))

theorem tiltedWeight_mean (x : ℝ) :
    spinMean (tiltedWeight x : (ι → Bool) → ℝ) = 1 := by
  unfold spinMean tiltedWeight
  rw [← Fintype.prod_sum (fun (_i : ι) (b : Bool) => (1 + x * spinSign b))]
  have hbit : (∑ b : Bool, (1 + x * spinSign b)) = 2 := by
    simp [spinSign]
    ring
  simp only [hbit, Finset.prod_const, Finset.card_univ]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

theorem tiltedWeight_pos {x : ℝ} (hx : -1 < x) (hx1 : x < 1) (σ : ι → Bool) :
    0 < tiltedWeight x σ := by
  apply Finset.prod_pos
  intro i _
  cases h : σ i <;> simp [spinSign, h] <;> linarith

/-- Logarithm of the tilt, with the overlap displayed explicitly. -/
theorem log_tiltedWeight {x : ℝ} (hx : -1 < x) (hx1 : x < 1)
    (hι : 0 < Fintype.card ι) (σ : ι → Bool) :
    Real.log (tiltedWeight x σ) = (Fintype.card ι : ℝ) *
      (entropy x + (overlap σ - x) / 2 * (Real.log (1 + x) - Real.log (1 - x))) := by
  have hfac : ∀ i, (1 + x * spinSign (σ i)) ≠ 0 := by
    intro i
    cases h : σ i <;> simp [spinSign, h] <;> linarith
  unfold tiltedWeight
  rw [Real.log_prod (fun i _ => hfac i)]
  have hlog : ∀ i, Real.log (1 + x * spinSign (σ i)) =
      (Real.log (1 + x) + Real.log (1 - x)) / 2 +
      spinSign (σ i) * ((Real.log (1 + x) - Real.log (1 - x)) / 2) := by
    intro i
    cases h : σ i <;> simp [spinSign, h] <;> ring
  simp_rw [hlog]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold entropy overlap signSum
  field_simp [ne_of_gt (Nat.cast_pos.mpr hι : (0 : ℝ) < Fintype.card ι)]
  <;> ring

/-- Monotonicity of the actual finite uniform average. -/
theorem mean_mono {f g : (ι → Bool) → ℝ} (h : ∀ σ, f σ ≤ g σ) :
    spinMean f ≤ spinMean g := by
  unfold spinMean
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _ => h σ))
    (by positivity)

/-- The finite-cube probability of a predicate. -/
def cubeProbability (P : (ι → Bool) → Prop) [DecidablePred P] : ℝ :=
  spinMean (fun σ => if P σ then 1 else 0)

theorem cubeProbability_eq_card (P : (ι → Bool) → Prop) [DecidablePred P] :
    cubeProbability P = ((Finset.univ.filter P).card : ℝ) / (2 : ℝ)^Fintype.card ι := by
  unfold cubeProbability spinMean
  rw [Finset.sum_boole]
  ring

/-- Chernoff's estimate at every nonendpoint positive threshold, with the
exact entropy and its exact constant. -/
theorem overlap_chernoff_lt_one (hι : 0 < Fintype.card ι) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) :
    cubeProbability (fun σ : ι → Bool => x ≤ overlap σ) ≤
      Real.exp (-(Fintype.card ι : ℝ) * entropy x) := by
  have hneg : -1 < x := by linarith
  have hlogs : 0 ≤ Real.log (1 + x) - Real.log (1 - x) := by
    exact sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have hind : ∀ σ : ι → Bool,
      (if x ≤ overlap σ then (1 : ℝ) else 0) ≤
      Real.exp (-(Fintype.card ι : ℝ) * entropy x) * tiltedWeight x σ := by
    intro σ
    by_cases hσ : x ≤ overlap σ
    · rw [if_pos hσ]
      have hlog := log_tiltedWeight hneg hx1 hι σ
      have hinc : 0 ≤ (overlap σ - x) / 2 *
          (Real.log (1 + x) - Real.log (1 - x)) :=
        mul_nonneg (div_nonneg (sub_nonneg.mpr hσ) (by norm_num)) hlogs
      have hbase : (Fintype.card ι : ℝ) * entropy x ≤
          Real.log (tiltedWeight x σ) := by
        rw [hlog]
        exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      have hexp := Real.exp_le_exp.mpr hbase
      rw [Real.exp_log (tiltedWeight_pos hneg hx1 σ)] at hexp
      calc
        1 = Real.exp (-(Fintype.card ι : ℝ) * entropy x) *
            Real.exp ((Fintype.card ι : ℝ) * entropy x) := by
          rw [← Real.exp_add]
          simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    · rw [if_neg hσ]
      exact mul_nonneg (Real.exp_pos _).le (tiltedWeight_pos hneg hx1 σ).le
  have h := mean_mono hind
  rw [spinMean_mul_left, tiltedWeight_mean, mul_one] at h
  exact h

/-- The endpoint overlap is attained only by the all-positive spin configuration. -/
theorem all_spins_one_of_one_le_overlap (hι : 0 < Fintype.card ι)
    (σ : ι → Bool) (hσ : 1 ≤ overlap σ) : ∀ i, spinSign (σ i) = 1 := by
  have hsum : (Fintype.card ι : ℝ) ≤ ∑ i, spinSign (σ i) := by
    simpa only [one_mul, signSum] using (le_div_iff₀ (Nat.cast_pos.mpr hι)).mp hσ
  have hdef : ∀ i, 0 ≤ 1 - spinSign (σ i) := by
    intro i
    have := (abs_le.mp (le_of_eq (abs_spinSign (σ i)))).2
    linarith
  intro i
  have hs := Finset.single_le_sum (s := Finset.univ) (f := fun j => 1 - spinSign (σ j))
    (fun j _ => hdef j) (Finset.mem_univ i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hs
  linarith [hdef i]

/-- Chernoff at the endpoint `x=1`, without invoking a limiting convention. -/
theorem overlap_chernoff_one (hι : 0 < Fintype.card ι) :
    cubeProbability (fun σ : ι → Bool => 1 ≤ overlap σ) ≤
      Real.exp (-(Fintype.card ι : ℝ) * entropy 1) := by
  have hexp : Real.exp (-(Fintype.card ι : ℝ) * entropy 1) =
      ((2 : ℝ)^Fintype.card ι)⁻¹ := by
    rw [entropy_one, neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hexp]
  have hpoint : ∀ σ : ι → Bool,
      (if 1 ≤ overlap σ then (1 : ℝ) else 0) ≤
      ((2 : ℝ)^Fintype.card ι)⁻¹ * tiltedWeight 1 σ := by
    intro σ
    split_ifs with hσ
    · have hall := all_spins_one_of_one_le_overlap hι σ hσ
      simp only [tiltedWeight, hall, mul_one, one_add_one_eq_two, Finset.prod_const, Finset.card_univ]
      rw [inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0))]
    · apply mul_nonneg (by positivity)
      apply Finset.prod_nonneg
      intro i _
      cases σ i <;> norm_num [spinSign]
  have h := mean_mono hpoint
  rw [spinMean_mul_left, tiltedWeight_mean, mul_one] at h
  exact h

/-- Exact one-sided finite Rademacher Chernoff, including both endpoints. -/
theorem overlap_chernoff (hι : 0 < Fintype.card ι) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    cubeProbability (fun σ : ι → Bool => x ≤ overlap σ) ≤
      Real.exp (-(Fintype.card ι : ℝ) * entropy x) := by
  obtain hlt | rfl := hx1.lt_or_eq
  · exact overlap_chernoff_lt_one hι hx hlt
  · exact overlap_chernoff_one hι

/-- The sign-reversing bijection of the finite cube. -/
def complementEquiv : (ι → Bool) ≃ (ι → Bool) where
  toFun σ i := !(σ i)
  invFun σ i := !(σ i)
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

@[simp] theorem overlap_complement (σ : ι → Bool) :
    overlap (complementEquiv σ) = -overlap σ := by
  have hsign : ∀ i, spinSign (!(σ i)) = -spinSign (σ i) := by
    intro i
    cases σ i <;> norm_num [spinSign]
  simp [overlap, signSum, complementEquiv, hsign, Finset.sum_neg_distrib, neg_div]

theorem mean_complement (f : (ι → Bool) → ℝ) :
    spinMean (fun σ => f (complementEquiv σ)) = spinMean f := by
  unfold spinMean
  congr 1
  exact Fintype.sum_equiv complementEquiv _ _ (fun _ => rfl)

/-- Exact two-sided Chernoff for the absolute overlap. -/
theorem abs_overlap_chernoff (hι : 0 < Fintype.card ι) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    cubeProbability (fun σ : ι → Bool => x ≤ |overlap σ|) ≤
      2 * Real.exp (-(Fintype.card ι : ℝ) * entropy x) := by
  have hnegative : cubeProbability (fun σ : ι → Bool => overlap σ ≤ -x) =
      cubeProbability (fun σ : ι → Bool => x ≤ overlap σ) := by
    unfold cubeProbability
    rw [← mean_complement (fun σ : ι → Bool => if overlap σ ≤ -x then 1 else 0)]
    simp only [overlap_complement, neg_le_neg_iff]
  have hpoint : ∀ σ : ι → Bool,
      (if x ≤ |overlap σ| then (1 : ℝ) else 0) ≤
      (if x ≤ overlap σ then (1 : ℝ) else 0) +
        (if overlap σ ≤ -x then (1 : ℝ) else 0) := by
    intro σ
    split_ifs with habs hpos hneg hneg hpos hneg hneg <;> try norm_num
    have ha : |overlap σ| < x := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have h := mean_mono hpoint
  have hadd : spinMean (fun σ : ι → Bool =>
      (if x ≤ overlap σ then (1 : ℝ) else 0) +
        (if overlap σ ≤ -x then (1 : ℝ) else 0)) =
      cubeProbability (fun σ : ι → Bool => x ≤ overlap σ) +
      cubeProbability (fun σ : ι → Bool => overlap σ ≤ -x) := by
    simp [spinMean, cubeProbability, Finset.sum_add_distrib, mul_add]
  rw [hadd, hnegative] at h
  have hc := overlap_chernoff hι hx hx1
  change cubeProbability (fun σ : ι → Bool => x ≤ |overlap σ|) ≤ _ at h
  linarith

@[simp] theorem entropy_abs (x : ℝ) : entropy |x| = entropy x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, entropy_neg]

/-- The exact entropy tail on the actual cube. The finite minimum argument
handles the discontinuous distribution and both overlap endpoints directly. -/
theorem entropy_tail (hι : 0 < Fintype.card ι) {t : ℝ} (ht : 0 ≤ t) :
    cubeProbability (fun σ : ι → Bool => t ≤ (Fintype.card ι : ℝ) * entropy (overlap σ)) ≤
      2 * Real.exp (-t) := by
  classical
  let S := Finset.univ.filter (fun σ : ι → Bool => t ≤ (Fintype.card ι : ℝ) * entropy (overlap σ))
  by_cases hS : S.Nonempty
  · obtain ⟨σ₀, hσ₀, hmin⟩ := S.exists_min_image (fun σ => |overlap σ|) hS
    have hpoint : ∀ σ : ι → Bool,
        (if t ≤ (Fintype.card ι : ℝ) * entropy (overlap σ) then (1 : ℝ) else 0) ≤
        (if |overlap σ₀| ≤ |overlap σ| then (1 : ℝ) else 0) := by
      intro σ
      by_cases hσ : t ≤ (Fintype.card ι : ℝ) * entropy (overlap σ)
      · rw [if_pos hσ, if_pos (hmin σ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hσ⟩))]
      · rw [if_neg hσ]
        split_ifs <;> norm_num
    have hcompare := mean_mono hpoint
    have hc := abs_overlap_chernoff hι (abs_nonneg (overlap σ₀))
      (abs_overlap_le_one hι σ₀)
    have hthreshold : t ≤ (Fintype.card ι : ℝ) * entropy (overlap σ₀) :=
      (Finset.mem_filter.mp hσ₀).2
    have hexp : Real.exp (-(Fintype.card ι : ℝ) * entropy |overlap σ₀|) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      rw [entropy_abs]
      linarith
    exact hcompare.trans (hc.trans (mul_le_mul_of_nonneg_left hexp (by norm_num)))
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [cubeProbability_eq_card]
    change (S.card : ℝ) / (2 : ℝ)^Fintype.card ι ≤ _
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

/-- The squared graphical second-moment threshold, exactly as in (4). -/
def thresholdSquared (p : ℕ) : ℝ :=
  sInf ((fun x : ℝ => (Nat.factorial p : ℝ) * entropy x / x^p) '' Set.Ioc 0 1)

/-- The set defining the threshold is nonempty; `x=1` is permitted. -/
theorem threshold_set_nonempty (p : ℕ) :
    ((fun x : ℝ => (Nat.factorial p : ℝ) * entropy x / x^p) '' Set.Ioc 0 1).Nonempty := by
  exact Set.Nonempty.image _ ⟨1, by norm_num⟩

/-- Nonnegative entropy provides a genuine lower bound for the infimum. -/
theorem threshold_set_bddBelow (p : ℕ) :
    BddBelow ((fun x : ℝ => (Nat.factorial p : ℝ) * entropy x / x^p) '' Set.Ioc 0 1) := by
  refine ⟨0, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (entropy_nonneg x)) (pow_nonneg hx.1.le _)

theorem thresholdSquared_nonneg (p : ℕ) : 0 ≤ thresholdSquared p := by
  apply le_csInf (threshold_set_nonempty p)
  rintro y ⟨x, hx, rfl⟩
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (entropy_nonneg x)) (pow_nonneg hx.1.le _)

/-- The exact threshold is at most the endpoint entropy `p! log 2`. -/
theorem thresholdSquared_le (p : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    thresholdSquared p ≤ (Nat.factorial p : ℝ) * entropy x / x^p := by
  exact csInf_le (threshold_set_bddBelow p) ⟨x, ⟨hx, hx1⟩, rfl⟩

theorem thresholdSquared_le_factorial_log_two (p : ℕ) :
    thresholdSquared p ≤ (Nat.factorial p : ℝ) * Real.log 2 := by
  simpa using thresholdSquared_le p (by norm_num : (0:ℝ) < 1) le_rfl

/-- The key variational inequality uses the full paper threshold. It remains
valid for negative overlaps and odd interaction order. -/
theorem scaled_overlap_power_le_entropy {p : ℕ} (hp : 0 < p)
    {v x : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared p) (hx : |x| ≤ 1) :
    v * x^p / (Nat.factorial p : ℝ) ≤ (v / thresholdSquared p) * entropy x := by
  have hT : 0 < thresholdSquared p := lt_of_le_of_lt hv hvT
  have hfac : (0 : ℝ) < (Nat.factorial p : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  by_cases hx0 : x = 0
  · subst x
    simp [hp.ne']
  have habs : 0 < |x| := abs_pos.mpr hx0
  have hbase := thresholdSquared_le p habs hx
  have hmul : thresholdSquared p * |x|^p ≤ (Nat.factorial p : ℝ) * entropy x := by
    have h := (le_div_iff₀ (pow_pos habs p)).mp hbase
    simpa only [entropy_abs] using h
  have hpow : x^p ≤ |x|^p := by simpa only [abs_pow] using le_abs_self (x^p)
  calc
    v * x^p / (Nat.factorial p : ℝ) ≤ v * |x|^p / (Nat.factorial p : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hv) hfac.le
    _ ≤ (v / thresholdSquared p) * entropy x := by
      apply (div_le_iff₀ hfac).mpr
      have h := mul_le_mul_of_nonneg_left hmul (div_nonneg hv hT.le)
      have heq : v / thresholdSquared p * (thresholdSquared p * |x|^p) = v * |x|^p := by
        field_simp
      rw [heq] at h
      nlinarith

end SpinGlass.UniformMassEntropy
