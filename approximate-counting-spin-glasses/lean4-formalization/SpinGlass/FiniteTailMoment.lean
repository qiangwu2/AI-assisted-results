import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integrating a finite exponential tail

This is the finite weighted tail-to-moment calculation used after the entropy
Chernoff estimate. It proves the precise factor `1 + 2*lam/(1-lam)` by integrating
actual tail indicators, not by assuming an exponential moment bound.
-/

noncomputable section

namespace SpinGlass.FiniteTailMoment

open Finset Set MeasureTheory
open scoped BigOperators

theorem exp_derivative_integral (a b : ℝ) :
    (∫ t in 0..b, a * Real.exp (a * t)) = Real.exp (a * b) - 1 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun x : ℝ => Real.exp (a * x))
      (a * Real.exp (a * t)) t := by
    intro t
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
      (Real.hasDerivAt_exp (a * t)).comp t ((hasDerivAt_id t).const_mul a)
  have hi : IntervalIntegrable (fun t : ℝ => a * Real.exp (a * t)) volume 0 b :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi

theorem decay_integral_le {lam : ℝ} (hlam : lam < 1) (M : ℝ) :
    (∫ t in 0..M, Real.exp ((lam - 1) * t)) ≤ 1 / (1 - lam) := by
  have h := exp_derivative_integral (lam - 1) M
  rw [intervalIntegral.integral_const_mul] at h
  apply (le_div_iff₀ (by linarith : 0 < 1 - lam)).2
  nlinarith [Real.exp_pos ((lam - 1) * M)]

/-- Every finite nonnegative random variable with tail at most `2 exp(-t)`
has the claimed exponential moment, for every `0 ≤ lam < 1`. -/
theorem finite_exponential_moment {Ω : Type*} [Fintype Ω]
    (w T : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (hT : ∀ ω, 0 ≤ T ω)
    (htail : ∀ t : ℝ, 0 ≤ t → (∑ ω with t ≤ T ω, w ω) ≤ 2 * Real.exp (-t))
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    (∑ ω, w ω * Real.exp (lam * T ω)) ≤ 1 + 2 * lam / (1 - lam) := by
  classical
  let M : ℝ := ∑ ω, T ω
  let g : ℝ → ℝ := fun t => lam * Real.exp (lam * t)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun ω _ => hT ω)
  have hTM : ∀ ω, T ω ≤ M := fun ω =>
    Finset.single_le_sum (fun ω _ => hT ω) (Finset.mem_univ ω)
  have hg : IntervalIntegrable g volume 0 M :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi : ∀ ω, IntervalIntegrable ((Iic (T ω)).indicator g) volume 0 M := by
    intro ω
    exact ⟨hg.1.indicator measurableSet_Iic, hg.2.indicator measurableSet_Iic⟩
  have hwi : ∀ ω, IntervalIntegrable (fun t => w ω * (Iic (T ω)).indicator g t) volume 0 M :=
    fun ω => (hi ω).const_mul (w ω)
  have hid : (∫ t in 0..M, ∑ ω, w ω * (Iic (T ω)).indicator g t) =
      (∑ ω, w ω * Real.exp (lam * T ω)) - 1 := by
    rw [intervalIntegral.integral_finsetSum (fun ω _ => hwi ω)]
    simp_rw [intervalIntegral.integral_const_mul]
    have hatom : ∀ ω, (∫ t in 0..M, (Iic (T ω)).indicator g t) =
        Real.exp (lam * T ω) - 1 := by
      intro ω
      change (∫ t in 0..M, ({x : ℝ | x ≤ T ω}).indicator g t) = _
      rw [intervalIntegral.integral_indicator (f := g) (μ := volume) ⟨hT ω, hTM ω⟩]
      exact exp_derivative_integral lam (T ω)
    simp_rw [hatom, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hsum]
  have hpoint : ∀ t : ℝ, 0 ≤ t →
      (∑ ω, w ω * (Iic (T ω)).indicator g t) ≤
        (2 * lam) * Real.exp ((lam - 1) * t) := by
    intro t ht
    have heq : (∑ ω, w ω * (Iic (T ω)).indicator g t) =
        g t * (∑ ω with t ≤ T ω, w ω) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases he : t ≤ T ω <;> simp [Set.indicator, he, mul_comm]
    rw [heq]
    calc
      g t * (∑ ω with t ≤ T ω, w ω) ≤ g t * (2 * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left (htail t ht) (mul_nonneg hlam (Real.exp_pos _).le)
      _ = (2 * lam) * Real.exp ((lam - 1) * t) := by
        dsimp [g]
        rw [show (lam - 1) * t = lam * t + -t by ring, Real.exp_add]
        ring
  have hup : IntervalIntegrable (fun t : ℝ => (2 * lam) * Real.exp ((lam - 1) * t)) volume 0 M :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hsumI : IntervalIntegrable (fun t => ∑ ω, w ω * (Iic (T ω)).indicator g t) volume 0 M := by
    exact ⟨integrable_finsetSum Finset.univ (fun ω _ => (hwi ω).1),
      integrable_finsetSum Finset.univ (fun ω _ => (hwi ω).2)⟩
  have hbound := intervalIntegral.integral_mono_on hM hsumI hup
    (fun t ht => hpoint t ht.1)
  rw [hid, intervalIntegral.integral_const_mul] at hbound
  have hdecay := mul_le_mul_of_nonneg_left (decay_integral_le hlam1 M)
    (by positivity : 0 ≤ 2 * lam)
  have hcombined := hbound.trans hdecay
  have hr : 2 * lam * (1 / (1 - lam)) = 2 * lam / (1 - lam) := by ring
  rw [hr] at hcombined
  linarith

end SpinGlass.FiniteTailMoment
