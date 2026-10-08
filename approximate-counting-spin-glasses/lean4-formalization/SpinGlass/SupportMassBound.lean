import SpinGlass.SupportMassCounting
import SpinGlass.SupportScalar
import Mathlib.Algebra.BigOperators.Intervals

/-! Uniform estimates for the growing-support squared mass. -/

noncomputable section
namespace SpinGlass.SupportMassBound
open Finset Real
open SpinGlass.SupportMassCounting

/-- Turning the finite binomial tail into the explicit Poisson-tail expression. -/
theorem binomial_tail_le_poisson (M m : ℕ) {r : ℝ} (hr : 0 ≤ r) (hm : 0 < m) :
    (∑ k ∈ (Finset.range (M+1)).filter (fun k => m ≤ k), (M.choose k : ℝ) * r^k) ≤
      Real.exp ((M : ℝ)*r) * (Real.exp 1 * ((M : ℝ)*r) / m)^m := by
  calc
    _ ≤ ∑ k ∈ (Finset.range (M+1)).filter (fun k => m ≤ k),
        ((M : ℝ)*r)^k / k.factorial := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        (M.choose k : ℝ) * r^k ≤ ((M : ℝ)^k / k.factorial) * r^k :=
          mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k M) (pow_nonneg hr _)
        _ = _ := by rw [mul_pow]; ring
    _ = ∑ j ∈ Finset.range (M+1-m), ((M : ℝ)*r)^(m+j) / (m+j).factorial := by
      rw [show (Finset.range (M+1)).filter (fun k => m ≤ k) = Finset.Ico m (M+1) by
        ext k; simp; omega]
      rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ _ := SpinGlass.SupportScalar.finite_poisson_tail_exp (mul_nonneg (Nat.cast_nonneg _) hr) hm _

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The support-mass inequality (50), uniformly in all support sizes. -/
theorem supportMass_le_poisson {p v : ℕ} (hp : 0 < p) (hv : 0 < v)
    {r : ℝ} (hr : 0 ≤ r) :
    supportMass (V := V) p v r ≤ ((Fintype.card V).choose v : ℝ) *
      Real.exp ((v.choose p : ℝ)*r) *
        (Real.exp 1 * ((v.choose p : ℝ)*r) / minEdges p v)^(minEdges p v) := by
  have hm : 0 < minEdges p v := by
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hv)) (Nat.cast_pos.mpr hp)
  have h := supportMass_le_binomial_tail (V := V) (v := v) hp hr
  have hb := mul_le_mul_of_nonneg_left (binomial_tail_le_poisson (v.choose p) (minEdges p v) hr hm)
    (Nat.cast_nonneg ((Fintype.card V).choose v) : (0:ℝ) ≤ _)
  exact h.trans (by simpa only [mul_assoc] using hb)

/-- The two paper constants preceding the support-mass bound. -/
def dZero (p : ℕ) (B : ℝ) : ℝ := B^2 / (p.factorial : ℝ)
def aZero (p : ℕ) (B : ℝ) : ℝ := Real.exp 1 * dZero p B * p / 2

/-- The Poisson parameter has the required uniform dependence on support size. -/
theorem poisson_parameter_bound {p v N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {B r : ℝ} (hr : 0 ≤ r) (hrB : r ≤ B^2 / (N : ℝ)^(p-1)) :
    (v.choose p : ℝ)*r ≤ dZero p B * v * ((v : ℝ)/N)^(p-1) := by
  have hfac : (0 : ℝ) < p.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hvpow : (v : ℝ)^p = (v : ℝ)*(v : ℝ)^(p-1) := by
    rw [← pow_succ']; congr 1; omega
  calc
    (v.choose p : ℝ)*r ≤ ((v : ℝ)^p / p.factorial) * r :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div p v) hr
    _ ≤ ((v : ℝ)^p / p.factorial) * (B^2/(N : ℝ)^(p-1)) :=
      mul_le_mul_of_nonneg_left hrB (div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hfac.le)
    _ = _ := by
      unfold dZero
      rw [div_pow, hvpow]
      ring

/-- The ceiling in the minimum-edge count is bounded below by its defining ratio. -/
theorem ratio_le_minEdges {p v : ℕ} : (2 : ℝ)*v/p ≤ (minEdges p v : ℝ) :=
  Nat.le_ceil _

/-- The base appearing in the Poisson tail is small at the paper's support scale. -/
theorem poisson_base_bound {p v N : ℕ} (hp : 0 < p) (hv : 0 < v) (hN : 0 < N)
    {B r : ℝ} (hr : 0 ≤ r) (hrB : r ≤ B^2 / (N : ℝ)^(p-1)) :
    Real.exp 1 * ((v.choose p : ℝ)*r) / minEdges p v ≤
      aZero p B * ((v : ℝ)/N)^(p-1) := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  have hm : 0 < (minEdges p v : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos (by norm_num) hvR) hpR) ratio_le_minEdges
  have hparam := poisson_parameter_bound (v := v) hp hN hr hrB
  have hratio := (div_le_iff₀ hpR).mp (ratio_le_minEdges (p := p) (v := v))
  have hfactor : 0 ≤ Real.exp 1 * dZero p B * ((v : ℝ)/N)^(p-1) := by
    unfold dZero
    positivity
  have hprod := mul_le_mul_of_nonneg_left hratio hfactor
  apply (div_le_iff₀ hm).mpr
  have he := mul_le_mul_of_nonneg_left hparam (Real.exp_pos 1).le
  unfold aZero
  nlinarith

/-- The exponent in the paper's support estimate. -/
def kappa (p : ℕ) : ℝ := ((p : ℝ) - 2) / p
/-- The coefficient before taking the maximum with one. -/
def rawSupportConstant (p : ℕ) (B : ℝ) : ℝ :=
  Real.exp (1 + dZero p B) * (aZero p B) ^ (2 / (p : ℝ))
/-- The paper's `A_p`. -/
def supportConstant (p : ℕ) (B : ℝ) : ℝ := max 1 (rawSupportConstant p B)
/-- The paper's `a_p`. -/
def supportScale (p : ℕ) (B : ℝ) : ℝ := (supportConstant p B) ^ (1 / kappa p)

theorem dZero_pos (p : ℕ) {B : ℝ} (hB : 0 < B) : 0 < dZero p B := by
  unfold dZero
  positivity

theorem aZero_pos {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 < B) : 0 < aZero p B := by
  unfold aZero
  exact div_pos (mul_pos (mul_pos (Real.exp_pos 1) (dZero_pos p hB)) (Nat.cast_pos.mpr hp)) (by norm_num)

/-- Algebraic identity that matches the enumeration scale to the omitted mass. -/
theorem support_scale_identity {p v N : ℕ} (hp : 0 < p) (hv : 0 < v) (hN : 0 < N)
    {B : ℝ} (hB : 0 < B) :
    (Real.exp 1 * N / v)^v * Real.exp (dZero p B * v) *
      (aZero p B * ((v : ℝ)/N)^(p-1))^((2 : ℝ)*v/p) =
      (rawSupportConstant p B * ((v : ℝ)/N)^(kappa p))^v := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have ha := aZero_pos hp hB
  have ht : 0 < (v : ℝ)/N := div_pos hvR hNR
  have hl : 0 < (Real.exp 1 * N / v)^v * Real.exp (dZero p B * v) *
      (aZero p B * ((v : ℝ)/N)^(p-1))^((2 : ℝ)*v/p) := by positivity
  have hr : 0 < (rawSupportConstant p B * ((v : ℝ)/N)^(kappa p))^v := by
    unfold rawSupportConstant
    positivity
  apply Real.log_injOn_pos hl hr
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_div (by positivity) hvR.ne', Real.log_mul (Real.exp_pos 1).ne' hNR.ne',
    Real.log_exp, Real.log_exp, Real.log_rpow (by positivity),
    Real.log_mul ha.ne' (pow_pos ht _).ne', Real.log_pow,
    Real.log_div hvR.ne' hNR.ne', Real.log_pow]
  unfold rawSupportConstant kappa
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos ha _).ne', Real.log_exp,
    Real.log_rpow ha, Real.log_rpow ht, Real.log_div hvR.ne' hNR.ne']
  rw [Nat.cast_sub hp]
  push_cast
  field_simp
  <;> ring

/-- Lemma 5.2: the support-mass bound with the paper's explicit growing-support scale. -/
theorem supportMass_bound {p v N : ℕ} (hcard : Fintype.card V = N)
    (hp : 3 ≤ p) (hpN : p ≤ N) (hv : 0 < v)
    {B r alpha : ℝ} (hB : 0 < B) (hr : 0 ≤ r)
    (hrB : r ≤ B^2/(N : ℝ)^(p-1)) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hsmall : aZero p B * alpha^(p-1) ≤ 1) (hvN : (v : ℝ) ≤ alpha*N) :
    supportMass (V := V) p v r ≤
      (supportConstant p B * ((v : ℝ)/N)^(kappa p))^v := by
  have hp0 : 0 < p := by omega
  have hN : 0 < N := lt_of_lt_of_le hp0 hpN
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp0
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have ht : 0 < (v : ℝ)/N := div_pos hvR hNR
  have hta : (v : ℝ)/N ≤ alpha := (div_le_iff₀ hNR).mpr hvN
  have ht1 : (v : ℝ)/N ≤ 1 := hta.trans halpha1
  have hd := (dZero_pos p hB).le
  have ha := (aZero_pos hp0 hB).le
  have hbase1 : aZero p B * ((v : ℝ)/N)^(p-1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hta _) ha).trans hsmall
  have hbase := poisson_base_bound hp0 hv hN hr hrB
  have hparam := poisson_parameter_bound (v := v) hp0 hN hr hrB
  have hlam : (v.choose p : ℝ)*r ≤ dZero p B*v :=
    hparam.trans (by nlinarith [(pow_le_one₀ (n := p-1) ht.le ht1), mul_nonneg hd hvR.le])
  have hm : 0 < (minEdges p v : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos (by norm_num) hvR) hpR) ratio_le_minEdges
  have hb0 : 0 ≤ Real.exp 1 * ((v.choose p : ℝ)*r) / minEdges p v := by positivity
  have hpow : (Real.exp 1 * ((v.choose p : ℝ)*r) / minEdges p v)^(minEdges p v) ≤
      (aZero p B * ((v : ℝ)/N)^(p-1))^((2:ℝ)*v/p) := by
    calc
      _ ≤ (aZero p B * ((v : ℝ)/N)^(p-1))^(minEdges p v) :=
        pow_le_pow_left₀ hb0 hbase _
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge' (mul_nonneg ha (pow_nonneg ht.le _))
          hbase1 (by positivity) ratio_le_minEdges
  have hstart := supportMass_le_poisson (V := V) hp0 hv hr
  rw [hcard] at hstart
  have hcomb := SpinGlass.SupportScalar.binomial_upper_bound N v
  have hexp := Real.exp_le_exp.mpr hlam
  have hbound : ((N.choose v : ℝ) * Real.exp ((v.choose p : ℝ)*r)) *
      (Real.exp 1 * ((v.choose p : ℝ)*r) / minEdges p v)^(minEdges p v) ≤
      (Real.exp 1 * N / v)^v * Real.exp (dZero p B*v) *
        (aZero p B * ((v : ℝ)/N)^(p-1))^((2:ℝ)*v/p) := by
    apply mul_le_mul _ hpow (pow_nonneg hb0 _) (by positivity)
    exact mul_le_mul hcomb hexp (Real.exp_pos _).le (by positivity)
  have hraw := hstart.trans hbound
  rw [support_scale_identity hp0 hv hN hB] at hraw
  apply hraw.trans
  apply pow_le_pow_left₀ (by unfold rawSupportConstant; positivity)
  exact mul_le_mul_of_nonneg_right (le_max_right 1 _) (Real.rpow_nonneg ht.le _)

theorem kappa_pos {p : ℕ} (hp : 3 ≤ p) : 0 < kappa p := by
  unfold kappa
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp
  exact div_pos (by linarith) (by linarith)

theorem one_le_supportConstant (p : ℕ) (B : ℝ) : 1 ≤ supportConstant p B := le_max_left _ _

theorem supportScale_pos (p : ℕ) (B : ℝ) : 0 < supportScale p B :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (one_le_supportConstant p B)) _

theorem one_le_supportScale {p : ℕ} (hp : 3 ≤ p) (B : ℝ) : 1 ≤ supportScale p B := by
  apply Real.one_le_rpow (one_le_supportConstant p B)
  exact div_nonneg zero_le_one (kappa_pos hp).le

/-- The power and exponential forms in (48) are exactly equal. -/
theorem support_bound_eq_exp {p v N : ℕ} (hp : 3 ≤ p) (hv : 0 < v) (hN : 0 < N) (B : ℝ) :
    (supportConstant p B * ((v : ℝ)/N)^(kappa p))^v =
      Real.exp (-kappa p * v * Real.log ((N : ℝ)/(supportScale p B * v))) := by
  have hk := kappa_pos hp
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hA : 0 < supportConstant p B := lt_of_lt_of_le zero_lt_one (one_le_supportConstant p B)
  have ha := supportScale_pos p B
  have ht : 0 < (v : ℝ)/N := div_pos hvR hNR
  rw [← Real.exp_log (by positivity : 0 < (supportConstant p B * ((v : ℝ)/N)^(kappa p))^v)]
  congr 1
  rw [Real.log_pow, Real.log_mul hA.ne' (Real.rpow_pos_of_pos ht _).ne', Real.log_rpow ht,
    Real.log_div hvR.ne' hNR.ne', Real.log_div hNR.ne' (mul_pos ha hvR).ne',
    Real.log_mul ha.ne' hvR.ne']
  unfold supportScale
  rw [Real.log_rpow hA]
  field_simp
  <;> ring

/-- The exact exponential form of Lemma 5.2, with the manuscript's `a_p`. -/
theorem supportMass_bound_exp {p v N : ℕ} (hcard : Fintype.card V = N)
    (hp : 3 ≤ p) (hpN : p ≤ N) (hv : 0 < v)
    {B r alpha : ℝ} (hB : 0 < B) (hr : 0 ≤ r)
    (hrB : r ≤ B^2/(N : ℝ)^(p-1)) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hsmall : aZero p B * alpha^(p-1) ≤ 1) (hvN : (v : ℝ) ≤ alpha*N) :
    supportMass (V := V) p v r ≤
      Real.exp (-kappa p * v * Real.log ((N : ℝ)/(supportScale p B * v))) := by
  have h := supportMass_bound hcard hp hpN hv hB hr hrB halpha halpha1 hsmall hvN
  rw [support_bound_eq_exp hp hv (by omega) B] at h
  exact h

end SpinGlass.SupportMassBound
