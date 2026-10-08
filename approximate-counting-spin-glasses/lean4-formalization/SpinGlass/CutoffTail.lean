import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The growing-support cutoff exponent and its actual finite geometric tail. -/

noncomputable section
namespace SpinGlass.CutoffTail
open Finset Real
open scoped BigOperators

def phi (kap a N t : ℝ) : ℝ := kap * t * Real.log (N / (a * t))

theorem hasDerivAt_phi {kap a N t : ℝ} (ha : 0 < a) (hN : 0 < N) (ht : 0 < t) :
    HasDerivAt (phi kap a N) (kap * (Real.log (N / (a * t)) - 1)) t := by
  have hdiv := (hasDerivAt_const t N).div ((hasDerivAt_id t).const_mul a)
    (mul_ne_zero ha.ne' ht.ne')
  have hlog := hdiv.log (div_ne_zero hN.ne' (mul_ne_zero ha.ne' ht.ne'))
  convert ((hasDerivAt_id t).const_mul kap).mul hlog using 1 <;>
    first | rfl | (simp only [id_eq, Pi.div_apply]; field_simp; ring)

theorem phi_growth {kap a N alpha x y : ℝ}
    (hkap : 0 ≤ kap) (ha : 0 < a) (hN : 0 < N) (halpha : 0 < alpha)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1))
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ alpha * N) :
    2 * (y - x) ≤ phi kap a N y - phi kap a N x := by
  have hd : ∀ t ∈ Set.Icc x y, HasDerivAt (phi kap a N)
      (kap * (Real.log (N / (a * t)) - 1)) t := by
    intro t ht
    exact hasDerivAt_phi ha hN (hx.trans_le ht.1)
  have hlo : ∀ t ∈ Set.Icc x y,
      2 ≤ kap * (Real.log (N / (a * t)) - 1) := by
    intro t ht
    have htpos := hx.trans_le ht.1
    have hrat : 1 / (a * alpha) ≤ N / (a * t) := by
      apply (div_le_div_iff₀ (mul_pos ha halpha) (mul_pos ha htpos)).2
      nlinarith [mul_le_mul_of_nonneg_left (ht.2.trans hy) ha.le]
    exact hgap.trans (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.log_le_log (by positivity) hrat) 1) hkap)
  apply (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact hlo t (interior_subset ht))
      x (by exact ⟨le_rfl, hxy⟩) y (by exact ⟨hxy, le_rfl⟩) hxy

theorem exp_neg_two_le_half : Real.exp (-2) ≤ (1 / 2 : ℝ) := by
  have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).2 (by linarith)

/-- All terms in the indicated support range are included; no asymptotic
qualification or assumed geometric tail is used. -/
theorem phi_tail {kap a N alpha : ℝ}
    (hkap : 0 ≤ kap) (ha : 0 < a) (hN : 0 < N) (halpha : 0 < alpha)
    (hgap : 2 ≤ kap * (Real.log (1 / (a * alpha)) - 1))
    {m K : ℕ} (hm : 1 ≤ m) (hK : (K : ℝ) ≤ alpha * N) :
    (∑ v ∈ Finset.Ico m (K + 1), Real.exp (-phi kap a N v)) ≤
      2 * Real.exp (-phi kap a N m) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpoint : ∀ v ∈ Finset.Ico m (K + 1),
      Real.exp (-phi kap a N v) ≤
        Real.exp (-phi kap a N m + 2 * m) * Real.exp (-2) ^ v := by
    intro v hv
    have hmv : (m : ℝ) ≤ v := by exact_mod_cast (Finset.mem_Ico.mp hv).1
    have hvK : (v : ℝ) ≤ K := by
      have := (Finset.mem_Ico.mp hv).2
      exact_mod_cast (show v ≤ K by omega)
    have hg := phi_growth hkap ha hN halpha hgap hmpos hmv (hvK.trans hK)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hq0 := (Real.exp_pos (-2)).le
  have hq1 : Real.exp (-2) < 1 := lt_of_le_of_lt exp_neg_two_le_half (by norm_num)
  have hgeom := geom_sum_Ico_le_of_lt_one (m := m) (n := K + 1) hq0 hq1
  have hcancel : Real.exp (-phi kap a N m + 2 * m) * Real.exp (-2) ^ m =
      Real.exp (-phi kap a N m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ∑ v ∈ Finset.Ico m (K + 1),
        Real.exp (-phi kap a N m + 2 * m) * Real.exp (-2) ^ v :=
      Finset.sum_le_sum hpoint
    _ = Real.exp (-phi kap a N m + 2 * m) *
        (∑ v ∈ Finset.Ico m (K + 1), Real.exp (-2) ^ v) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-phi kap a N m + 2 * m) *
        (Real.exp (-2) ^ m / (1 - Real.exp (-2))) :=
      mul_le_mul_of_nonneg_left hgeom (Real.exp_pos _).le
    _ = Real.exp (-phi kap a N m) / (1 - Real.exp (-2)) := by
      rw [← mul_div_assoc, hcancel]
    _ ≤ 2 * Real.exp (-phi kap a N m) := by
      apply (div_le_iff₀ (sub_pos.mpr hq1)).2
      nlinarith [Real.exp_pos (-phi kap a N m), exp_neg_two_le_half]

end SpinGlass.CutoffTail
