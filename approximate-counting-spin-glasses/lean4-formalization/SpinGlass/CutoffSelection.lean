import SpinGlass.CutoffTail
import SpinGlass.SupportScalar
import Mathlib.Algebra.Order.Floor.Semiring

/-! Uniform cutoff selection and the weighted binomial cost bound. -/

noncomputable section
namespace SpinGlass.CutoffSelection
open Finset Real
open SpinGlass.CutoffTail
open scoped BigOperators

def hZero (kap a alpha : ℝ) : ℝ := kap * alpha / 2 * Real.log (2 / (a * alpha))
def nu (kap a alpha omega : ℝ) : ℝ := min omega (min (hZero kap a alpha) 1) / 4
def costConstant (kap a alpha t : ℝ) : ℝ :=
  1 / kap + Real.log (Real.exp 1 * t * a) / (kap * Real.log (1 / (a * alpha)))

theorem log_gap_pos {kap a alpha : ℝ} (hkap : 0 < kap)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1)) :
    0 < Real.log (1 / (a * alpha)) := by
  by_contra h
  have := mul_nonpos_of_nonneg_of_nonpos hkap.le (show Real.log (1 / (a * alpha)) - 1 ≤ 0 by linarith)
  linarith

theorem hZero_pos {kap a alpha : ℝ} (hkap : 0 < kap) (ha : 0 < a) (halpha : 0 < alpha)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1)) :
    0 < hZero kap a alpha := by
  have hd := log_gap_pos hkap hgap
  have hh : 0 < Real.log (2 / (a * alpha)) :=
    hd.trans_le (Real.log_le_log (by positivity) (by gcongr; norm_num))
  exact mul_pos (div_pos (mul_pos hkap halpha) (by norm_num)) hh

theorem nu_pos {kap a alpha omega : ℝ} (hkap : 0 < kap) (ha : 0 < a)
    (halpha : 0 < alpha) (homega : 0 < omega)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1)) :
    0 < nu kap a alpha omega := by
  unfold nu
  exact div_pos (lt_min homega (lt_min (hZero_pos hkap ha halpha hgap) zero_lt_one)) (by norm_num)

theorem four_nu_le_omega (kap a alpha omega : ℝ) : 4 * nu kap a alpha omega ≤ omega := by
  unfold nu
  linarith [min_le_left omega (min (hZero kap a alpha) 1)]

theorem four_nu_le_hZero (kap a alpha omega : ℝ) :
    4 * nu kap a alpha omega ≤ hZero kap a alpha := by
  unfold nu
  linarith [min_le_right omega (min (hZero kap a alpha) 1), min_le_left (hZero kap a alpha) 1]

theorem phi_at_half {kap a alpha N : ℝ} (ha : 0 < a) (halpha : 0 < alpha) (hN : 0 < N) :
    phi kap a N (alpha * N / 2) = hZero kap a alpha * N := by
  have heq : N / (a * (alpha * N / 2)) = 2 / (a * alpha) := by field_simp
  simp only [phi, heq, hZero]
  ring

theorem floor_phi_lower {kap a alpha : ℝ} {N : ℕ}
    (hkap : 0 < kap) (ha : 0 < a) (halpha : 0 < alpha)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1))
    (hN : 2 / alpha ≤ (N : ℝ)) :
    1 ≤ Nat.floor (alpha * N) ∧
      hZero kap a alpha * N ≤ phi kap a N (Nat.floor (alpha * N)) := by
  have htwo : (2 : ℝ) ≤ alpha * N := (div_le_iff₀ halpha).mp hN |>.trans_eq (mul_comm _ _)
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hfloor : (Nat.floor (alpha * N) : ℝ) ≤ alpha * N := Nat.floor_le (by positivity)
  have hclose := Nat.lt_floor_add_one (alpha * (N : ℝ))
  have hhalf : alpha * (N : ℝ) / 2 ≤ Nat.floor (alpha * N) := by linarith
  constructor
  · have h1 : (1 : ℝ) ≤ Nat.floor (alpha * N) := by linarith
    exact_mod_cast h1
  · have hg := phi_growth hkap.le ha hNpos halpha hgap
      (show 0 < alpha * (N : ℝ) / 2 by positivity) hhalf hfloor
    rw [phi_at_half ha halpha hNpos] at hg
    linarith

/-- The first omitted size exists and every smaller positive size fails the
threshold. This minimality is the quantitative input to the cost proof. -/
theorem exists_first_omitted {kap a alpha omega Lambda : ℝ} {N : ℕ}
    (hkap : 0 < kap) (ha : 0 < a) (halpha : 0 < alpha)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1))
    (hN : 2 / alpha ≤ (N : ℝ)) (hLam : 0 < Lambda)
    (hsmall : Lambda < nu kap a alpha omega * N) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ Nat.floor (alpha * N) ∧ Lambda ≤ phi kap a N m ∧
      ∀ j : ℕ, 1 ≤ j → j < m → phi kap a N j < Lambda := by
  have hf := floor_phi_lower hkap ha halpha hgap hN
  have hNN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hlarge : Lambda ≤ phi kap a N (Nat.floor (alpha * N)) := by
    have hh := mul_le_mul_of_nonneg_right (four_nu_le_hZero kap a alpha omega) hNN
    nlinarith
  have hex : ∃ m : ℕ, 1 ≤ m ∧ m ≤ Nat.floor (alpha * N) ∧ Lambda ≤ phi kap a N m :=
    ⟨_, hf.1, le_rfl, hlarge⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1,
    (Nat.find_spec hex).2.2, ?_⟩
  intro j hj hjm
  by_contra hjbad
  have hnot := Nat.find_min hex hjm
  exact hnot ⟨hj, le_trans (Nat.le_of_lt hjm) (Nat.find_spec hex).2.1, le_of_not_gt hjbad⟩

theorem selected_error_bounds {kap a N alpha omega Lambda : ℝ} {m : ℕ}
    (hN : 0 ≤ N) (hLam : 0 ≤ Lambda)
    (hsmall : Lambda ≤ nu kap a alpha omega * N) (hm : Lambda ≤ phi kap a N m) :
    Real.exp (-phi kap a N m) ≤ Real.exp (-Lambda) ∧
      Real.exp (-omega * N) ≤ Real.exp (-4 * Lambda) := by
  constructor
  · exact Real.exp_le_exp.mpr (neg_le_neg hm)
  · have h := mul_le_mul_of_nonneg_right (four_nu_le_omega kap a alpha omega) hN
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem log_cost_nonneg {a t : ℝ} (ha : 1 ≤ a) (ht : 1 ≤ t) :
    0 ≤ Real.log (Real.exp 1 * t * a) := by
  apply Real.log_nonneg
  calc
    1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    _ ≤ Real.exp 1 * t * a := by
      have h1 := mul_le_mul_of_nonneg_left ht (Real.exp_pos 1).le
      have h2 := mul_le_mul_of_nonneg_left ha
        (mul_nonneg (Real.exp_pos 1).le (by linarith : 0 ≤ t))
      nlinarith

theorem costConstant_pos {kap a alpha t : ℝ} (hkap : 0 < kap) (ha : 1 ≤ a) (ht : 1 ≤ t)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1)) :
    0 < costConstant kap a alpha t := by
  exact add_pos_of_pos_of_nonneg (one_div_pos.mpr hkap)
    (div_nonneg (log_cost_nonneg ha ht) (mul_pos hkap (log_gap_pos hkap hgap)).le)

/-- A termwise cost estimate from minimality. It applies to every retained
size, avoiding any claim that an omitted size has the same cost. -/
theorem binomial_term_cost {kap a alpha t Lambda : ℝ} {N j : ℕ}
    (hkap : 0 < kap) (ha : 1 ≤ a) (halpha : 0 < alpha) (ht : 1 ≤ t)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1))
    (hN : 0 < N) (hj : 1 ≤ j) (hjalpha : (j : ℝ) ≤ alpha * N)
    (hjPhi : phi kap a N j ≤ Lambda) :
    (N.choose j : ℝ) * t^j ≤ Real.exp (costConstant kap a alpha t * Lambda) := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hd := log_gap_pos hkap hgap
  have hb := log_cost_nonneg ha ht
  have hrat : 1 / (a * alpha) ≤ (N : ℝ) / (a * j) := by
    apply (div_le_div_iff₀ (mul_pos ha0 halpha) (mul_pos ha0 hj0)).2
    nlinarith [mul_le_mul_of_nonneg_left hjalpha ha0.le]
  have hlog := Real.log_le_log (by positivity : 0 < 1 / (a * alpha)) hrat
  have hbase : kap * (j : ℝ) * Real.log (1 / (a * alpha)) ≤ phi kap a N j := by
    exact mul_le_mul_of_nonneg_left hlog (mul_pos hkap hj0).le
  have hjbound : (j : ℝ) ≤ phi kap a N j / (kap * Real.log (1 / (a * alpha))) := by
    apply (le_div_iff₀ (mul_pos hkap hd)).2
    nlinarith
  have hlogsplit : Real.log (Real.exp 1 * t * N / j) =
      Real.log ((N : ℝ) / (a * j)) + Real.log (Real.exp 1 * t * a) := by
    have heq : Real.exp 1 * t * N / j =
        ((N : ℝ) / (a * j)) * (Real.exp 1 * t * a) := by field_simp <;> ring
    rw [heq, Real.log_mul (by positivity) (by positivity)]
  have hexponent : (j : ℝ) * Real.log (Real.exp 1 * t * N / j) ≤
      costConstant kap a alpha t * Lambda := by
    calc
      _ = phi kap a N j / kap + j * Real.log (Real.exp 1 * t * a) := by
        rw [hlogsplit]
        unfold phi
        field_simp
        <;> ring
      _ ≤ phi kap a N j / kap +
          (phi kap a N j / (kap * Real.log (1 / (a * alpha)))) * Real.log (Real.exp 1 * t * a) := by
        gcongr
      _ = costConstant kap a alpha t * phi kap a N j := by unfold costConstant; ring
      _ ≤ costConstant kap a alpha t * Lambda :=
        mul_le_mul_of_nonneg_left hjPhi (costConstant_pos hkap ha ht hgap).le
  calc
    (N.choose j : ℝ) * t^j ≤ (Real.exp 1 * N / j)^j * t^j :=
      mul_le_mul_of_nonneg_right (SpinGlass.SupportScalar.binomial_upper_bound N j)
        (pow_nonneg ht0.le _)
    _ = (Real.exp 1 * t * N / j)^j := by rw [← mul_pow]; congr 1; ring
    _ = Real.exp ((j : ℝ) * Real.log (Real.exp 1 * t * N / j)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

/-- The full weighted binomial sum in Lemma 8.1, with an explicit constant. -/
theorem selected_binomial_cost {kap a alpha t Lambda : ℝ} {N m : ℕ}
    (hkap : 0 < kap) (ha : 1 ≤ a) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (ht : 1 ≤ t) (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1))
    (hN : 0 < N) (hLam : 0 ≤ Lambda) (hm : m ≤ Nat.floor (alpha * N))
    (hminimal : ∀ j : ℕ, 1 ≤ j → j < m → phi kap a N j < Lambda) :
    (∑ j ∈ Finset.range m, (N.choose j : ℝ) * t^j) ≤
      (N + 1) * Real.exp (costConstant kap a alpha t * Lambda) := by
  have hfloor : (Nat.floor (alpha * N) : ℝ) ≤ alpha * N := Nat.floor_le (by positivity)
  have hmN : (m : ℝ) ≤ (N : ℝ) := by
    have hmR : (m : ℝ) ≤ Nat.floor (alpha * N) := by exact_mod_cast hm
    nlinarith [mul_le_mul_of_nonneg_right halpha1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hpoint : ∀ j ∈ Finset.range m,
      (N.choose j : ℝ) * t^j ≤ Real.exp (costConstant kap a alpha t * Lambda) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
      exact Real.one_le_exp_iff.mpr (mul_nonneg (costConstant_pos hkap ha ht hgap).le hLam)
    · have hj1 : 1 ≤ j := by omega
      have hjm := Finset.mem_range.mp hj
      have hjalpha : (j : ℝ) ≤ alpha * N :=
        (by exact_mod_cast (le_trans (Nat.le_of_lt hjm) hm) : (j : ℝ) ≤ Nat.floor (alpha * N)).trans hfloor
      exact binomial_term_cost hkap ha halpha ht hgap hN hj1 hjalpha (hminimal j hj1 hjm).le
  calc
    _ ≤ ∑ _j ∈ Finset.range m, Real.exp (costConstant kap a alpha t * Lambda) :=
      Finset.sum_le_sum hpoint
    _ = (m : ℝ) * Real.exp (costConstant kap a alpha t * Lambda) := by simp
    _ ≤ (N + 1) * Real.exp (costConstant kap a alpha t * Lambda) := by gcongr; linarith

end SpinGlass.CutoffSelection
