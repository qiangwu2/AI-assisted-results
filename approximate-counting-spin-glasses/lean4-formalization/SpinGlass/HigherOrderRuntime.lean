import SpinGlass.HigherOrderAlgorithm

/-! Uniform runtime for the actual higher-order value evaluator. -/

noncomputable section
namespace SpinGlass.HigherOrderAlgorithm
open Finset Real
open SpinGlass.ArithmeticEvaluation SpinGlass.SupportEvaluation
open SpinGlass.SupportMassBound SpinGlass.DesignConstants SpinGlass.CutoffSelection
open SpinGlass.AlgorithmBudgets SpinGlass.PolynomialRuntime

def growth (p : ℕ) (B : ℝ) : ℝ :=
  max (costConstant (kappa p) (supportScale p B) (alpha p B) 3) (Real.log 2 / rate p B)
def amplitude (p : ℕ) (B : ℝ) : ℝ := ((p : ℝ)+10) * (2 : ℝ)^(sizeLimit p B)

theorem growth_pos {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    0 < growth p B := by
  have h := valid hp hB hBT
  exact (costConstant_pos (kappa_pos hp) (one_le_supportScale hp B) (by norm_num) h.gap).trans_le
    (le_max_left _ _)

theorem amplitude_ge (p : ℕ) (B : ℝ) : (p : ℝ)+10 ≤ amplitude p B := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ)^(sizeLimit p B) := one_le_pow₀ (by norm_num)
  dsimp [amplitude]
  nlinarith [(Nat.cast_nonneg p : (0:ℝ) ≤ p)]

theorem evaluator_envelope {p N : ℕ} (hp : 3 ≤ p) (hpN : p ≤ N) {B beta u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hu : 0 < u) (hu1 : u < 1)
    (J : Finset (Fin N) → ℝ) :
    ((run p N B beta u J).operations : ℝ) ≤
      amplitude p B * ((N : ℝ)+1)^(p+1) * Real.exp (growth p B * budget p B u) := by
  have hp0 : 0 < p := by omega
  have hN0 : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h := valid hp hB hBT
  have hLam : 0 < budget p B u := logBudget_pos h.budget_ge hu hu1
  have hg := growth_pos hp hB hBT
  have hA := amplitude_ge p B
  have hA0 : 0 ≤ amplitude p B := by linarith [(Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  have hsize : ((N : ℝ)+1)^p ≤ ((N : ℝ)+1)^(p+1) := by
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hexp : 1 ≤ Real.exp (growth p B * budget p B u) :=
    Real.one_le_exp_iff.mpr (mul_pos hg hLam).le
  by_cases he : exactBranch p N B u
  · have hcount := exactEvaluator_cost (V := Fin N) hp0
      (fun e => SpinGlass.Disorder.weight (SpinGlass.Disorder.pureScale N p beta) (J e))
    have hcountR : ((run p N B beta u J).operations : ℝ) ≤
        ((p : ℝ)+6)*((N : ℝ)+1)^p*(2 : ℝ)^N := by
      simp only [run, if_pos he]
      exact_mod_cast (by simpa only [Fintype.card_fin] using hcount)
    apply hcountR.trans
    rcases he with hsmall | hlarge
    · have h2 : (2 : ℝ)^N ≤ (2 : ℝ)^(sizeLimit p B) := pow_le_pow_right₀ (by norm_num) hsmall.le
      calc
        _ ≤ ((p : ℝ)+10)*((N : ℝ)+1)^(p+1)*(2 : ℝ)^(sizeLimit p B) := by gcongr; norm_num
        _ = amplitude p B * ((N : ℝ)+1)^(p+1) := by unfold amplitude; ring
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hexp
    · have h2 := exact_branch_cost h.rate_pos hlarge
      have hc : Real.log 2 / rate p B ≤ growth p B := le_max_right _ _
      have h2' : (2 : ℝ)^N ≤ Real.exp (growth p B * budget p B u) :=
        h2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc hLam.le))
      exact mul_le_mul (mul_le_mul (by linarith) hsize (by positivity) hA0) h2' (by positivity)
        (mul_nonneg hA0 (by positivity))
  · have hs := selectedSize_spec hp hB hBT hu hu1 he
    have hfloor : (Nat.floor (alpha p B * N) : ℝ) ≤ alpha p B * N :=
      Nat.floor_le (mul_nonneg h.alpha_pos.le (Nat.cast_nonneg _))
    have hmR : (selectedSize p N B u : ℝ) ≤ N := by
      have hm : (selectedSize p N B u : ℝ) ≤ Nat.floor (alpha p B * N) := by exact_mod_cast hs.2.1
      have ha := mul_le_mul_of_nonneg_right h.alpha_le (Nat.cast_nonneg N : (0:ℝ) ≤ N)
      nlinarith
    have hcut : selectedSize p N B u - 1 ≤ N := by
      have : selectedSize p N B u ≤ N := by exact_mod_cast hmR
      omega
    have hm : selectedSize p N B u - 1 + 1 = selectedSize p N B u := by omega
    have hcount := higherEvaluator_cost (V := Fin N) (cutoff := selectedSize p N B u - 1)
      hp0 (by simpa only [Fintype.card_fin] using hcut)
      (fun e => SpinGlass.Disorder.weight (SpinGlass.Disorder.pureScale N p beta) (J e))
    have hcountR : ((run p N B beta u J).operations : ℝ) ≤ ((p : ℝ)+10)*((N : ℝ)+1)^p *
        ∑ j ∈ Finset.range (selectedSize p N B u), (N.choose j : ℝ)*(3 : ℝ)^j := by
      simp only [run, if_neg he]
      exact_mod_cast (by simpa only [Fintype.card_fin, hm] using hcount)
    have hsum := selected_binomial_cost (kappa_pos hp) (one_le_supportScale hp B)
      h.alpha_pos h.alpha_le (by norm_num : (1:ℝ) ≤ 3) h.gap hN0 hLam.le hs.2.1 hs.2.2.2
    calc
      _ ≤ ((p : ℝ)+10)*((N : ℝ)+1)^p *
          (((N : ℝ)+1)*Real.exp (costConstant (kappa p) (supportScale p B) (alpha p B) 3 * budget p B u)) :=
        hcountR.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = ((p : ℝ)+10)*((N : ℝ)+1)^(p+1) *
          Real.exp (costConstant (kappa p) (supportScale p B) (alpha p B) 3 * budget p B u) := by
        rw [pow_succ]
        ring
      _ ≤ _ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hA (by positivity)
        · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hLam.le)
        · positivity
        · positivity

/-- The runtime exponent is fixed by `p,B`, uniformly over every accuracy and
every finite real input array. -/
theorem evaluator_polynomial {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B)
    (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), p ≤ N → ∀ (beta u : ℝ), 0 < u → u < 1 →
      ∀ J : Finset (Fin N) → ℝ,
      ((run p N B beta u J).operations : ℝ) ≤ C * (N : ℝ)^C * u^(-C) := by
  let C := envelopeConstant (amplitude p B) (budgetConstant p B) (growth p B) (p+1)
  refine ⟨C, envelopeConstant_pos _ _ _ _, ?_⟩
  intro N hpN beta u hu hu1 J
  have h := valid hp hB hBT
  exact (evaluator_envelope hp hpN hB hBT hu hu1 J).trans
    (envelope_le_polynomial (by dsimp [amplitude]; positivity) (by linarith [h.budget_ge])
      (by omega) hu hu1.le)

end SpinGlass.HigherOrderAlgorithm
