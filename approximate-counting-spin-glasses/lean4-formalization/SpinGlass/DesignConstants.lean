import SpinGlass.CutoffSelection
import SpinGlass.UniformMassEntropy

/-! Explicit choices of fixed design parameters. Their admissibility is proved,
so existence of a favorable cutoff scale is not an assumption of the algorithm. -/

noncomputable section
namespace SpinGlass.DesignConstants
open Real
open SpinGlass.CutoffSelection SpinGlass.UniformMassEntropy

def chosenAlpha (kap a K : ℝ) : ℝ :=
  min (1/8) (min (1/(K+1)) (Real.exp (-(1+2/kap))/a))

theorem chosenAlpha_pos {kap a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) :
    0 < chosenAlpha kap a K := by
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem chosenAlpha_le_eighth (kap a K : ℝ) : chosenAlpha kap a K ≤ 1/8 :=
  min_le_left _ _

theorem chosenAlpha_small {kap a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    {n : ℕ} (hn : 1 ≤ n) : K * chosenAlpha kap a K ^ n ≤ 1 := by
  have hpos := chosenAlpha_pos (kap := kap) ha hK
  have h1 : chosenAlpha kap a K ≤ 1 := (chosenAlpha_le_eighth _ _ _).trans (by norm_num)
  have hp : chosenAlpha kap a K ^ n ≤ chosenAlpha kap a K := by
    simpa using pow_le_pow_of_le_one hpos.le h1 hn
  have hinv : chosenAlpha kap a K ≤ 1/(K+1) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hm := mul_le_mul_of_nonneg_left hinv hK
  have hden : 0 < K+1 := by positivity
  have hdiv : K * (1/(K+1)) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hden).2 (by linarith)
  exact (mul_le_mul_of_nonneg_left hp hK).trans (hm.trans hdiv)

theorem chosenAlpha_gap {kap a K : ℝ} (hkap : 0 < kap) (ha : 0 < a) (hK : 0 ≤ K) :
    2 ≤ kap * (Real.log (1/(a*chosenAlpha kap a K))-1) := by
  have hpos := chosenAlpha_pos (kap := kap) ha hK
  have hc : chosenAlpha kap a K ≤ Real.exp (-(1+2/kap))/a :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmul : a * chosenAlpha kap a K ≤ Real.exp (-(1+2/kap)) := by
    have h := (le_div_iff₀ ha).mp hc
    simpa only [mul_comm] using h
  have hlog := Real.log_le_log (mul_pos ha hpos) hmul
  rw [Real.log_exp] at hlog
  have hinv : Real.log (1/(a*chosenAlpha kap a K)) =
      -Real.log (a*chosenAlpha kap a K) := by rw [one_div, Real.log_inv]
  rw [hinv]
  have h2 : kap * (2/kap) = 2 := by field_simp
  have h := mul_le_mul_of_nonneg_left hlog hkap.le
  nlinarith

def sizeThreshold (p : ℕ) (alpha : ℝ) : ℕ := Nat.ceil (max (p : ℝ) (max 4 (2/alpha)))

theorem sizeThreshold_ge_p (p : ℕ) (alpha : ℝ) : p ≤ sizeThreshold p alpha := by
  have h : (p : ℝ) ≤ sizeThreshold p alpha := (le_max_left _ _).trans (Nat.le_ceil _)
  exact_mod_cast h

theorem sizeThreshold_ge_four (p : ℕ) (alpha : ℝ) : 4 ≤ sizeThreshold p alpha := by
  have h : (4 : ℝ) ≤ sizeThreshold p alpha :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (Nat.le_ceil _)
  exact_mod_cast h

theorem sizeThreshold_ge_scale (p : ℕ) (alpha : ℝ) :
    2/alpha ≤ (sizeThreshold p alpha : ℝ) :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans (Nat.le_ceil _)

def betaThreshold (p : ℕ) : ℝ := Real.sqrt (thresholdSquared p)
def inflatedBeta (p : ℕ) (B : ℝ) : ℝ := (B + betaThreshold p) / 2

/-- The actual midpoint choice of inflated temperature lies strictly below
the full entropy threshold, with no strengthened temperature hypothesis. -/
theorem inflatedBeta_admissible {p : ℕ} {B : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) :
    B < inflatedBeta p B ∧ (inflatedBeta p B)^2 < thresholdSquared p := by
  have hs : betaThreshold p ^ 2 = thresholdSquared p := Real.sq_sqrt (thresholdSquared_nonneg p)
  have hmid : B < inflatedBeta p B := by unfold inflatedBeta; linarith
  have hupper : inflatedBeta p B < betaThreshold p := by unfold inflatedBeta; linarith
  exact ⟨hmid, by nlinarith⟩

end SpinGlass.DesignConstants
