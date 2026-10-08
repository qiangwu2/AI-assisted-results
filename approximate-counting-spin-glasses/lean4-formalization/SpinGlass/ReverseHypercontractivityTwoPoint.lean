import SpinGlass.ReverseHypercontractivityIngredients
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A proved two-point reverse-hypercontractive inequality

For positive input `(x,1)`, the r-power mean is bounded above by the
geometric mean of its noisy outputs when the noise correlation is at most
`1-r`. The proof identifies the actual first and second derivatives, invokes
the separately proved scalar curvature comparison, and uses tangency at `x=1`.
Homogeneity then gives the squared power-mean bound for any two positive inputs.
This module does not assert tensorization or the finite-cube negative-moment bound.
-/

noncomputable section
open Real Set

namespace SpinGlass.ReverseHypercontractivityTwoPoint

def powerMean (p x : ℝ) : ℝ := ((x ^ p + 1) / 2) ^ (1 / p)
def powerMeanDeriv (p x : ℝ) : ℝ :=
  (1 / 2) * ((x ^ p + 1) / 2) ^ (1 / p - 1) * x ^ (p - 1)
def powerMeanDeriv2 (p x : ℝ) : ℝ :=
  ((p - 1) / 4) * ((x ^ p + 1) / 2) ^ (1 / p - 2) * x ^ (p - 2)

lemma base_pos {p x : ℝ} (hx : 0 < x) : 0 < (x ^ p + 1) / 2 := by
  have := Real.rpow_pos_of_pos hx p
  positivity

lemma hasDerivAt_powerMean {p x : ℝ} (hp : p ≠ 0) (hx : 0 < x) :
    HasDerivAt (powerMean p) (powerMeanDeriv p x) x := by
  have hd := ((((hasDerivAt_id x).rpow_const (p := p) (Or.inl hx.ne')).add_const 1).div_const 2).rpow_const
    (p := 1 / p) (Or.inl (base_pos hx).ne')
  convert hd using 1
  · rfl
  · dsimp [powerMeanDeriv]
    field_simp

lemma hasDerivAt_powerMeanDeriv {p x : ℝ} (hp : p ≠ 0) (hx : 0 < x) :
    HasDerivAt (powerMeanDeriv p) (powerMeanDeriv2 p x) x := by
  let B : ℝ := (x ^ p + 1) / 2
  have hB : 0 < B := base_pos hx
  have h1 := ((((hasDerivAt_id x).rpow_const (p := p) (Or.inl hx.ne')).add_const 1).div_const 2).rpow_const
    (p := 1 / p - 1) (Or.inl hB.ne')
  have h2 := (hasDerivAt_id x).rpow_const (p := p - 1) (Or.inl hx.ne')
  have hd := (h1.const_mul (1 / 2 : ℝ)).mul h2
  have hBpow : B ^ (1 / p - 1) = B ^ (1 / p - 2) * B := by
    rw [show 1 / p - 1 = (1 / p - 2) + 1 by ring, Real.rpow_add hB, Real.rpow_one]
  have hxpow : x ^ (p - 1) * x ^ (p - 1) = x ^ (p - 2) * x ^ p := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  convert hd using 1 <;> try rfl
  change ((p - 1) / 4) * B ^ (1 / p - 2) * x ^ (p - 2) = _
  dsimp only [id_eq]
  change ((p - 1) / 4) * B ^ (1 / p - 2) * x ^ (p - 2) =
    (1 / 2) * ((1 * p * x ^ (p - 1)) / 2 * (1 / p - 1) * B ^ (1 / p - 1 - 1)) * x ^ (p - 1) +
    (1 / 2) * B ^ (1 / p - 1) * (1 * (p - 1) * x ^ (p - 1 - 1))
  rw [show 1 / p - 1 - 1 = 1 / p - 2 by ring,
    show p - 1 - 1 = p - 2 by ring, hBpow]
  calc
    _ = (p - 1) / 4 * B ^ (1 / p - 2) * x ^ (p - 2) := rfl
    _ = (1 - p) / 4 * B ^ (1 / p - 2) * (x ^ (p - 1) * x ^ (p - 1)) +
        (p - 1) / 2 * B ^ (1 / p - 2) * B * x ^ (p - 2) := by
      rw [hxpow]
      dsimp [B]
      ring
    _ = _ := by field_simp; ring

open SpinGlass.ReverseHypercontractivityIngredients

def noisyProductDeriv (θ x : ℝ) : ℝ := ((1 - θ ^ 2) * x + (1 + θ ^ 2)) / 2
def noisyMean (θ x : ℝ) : ℝ := noisyProduct θ x ^ (1 / 2 : ℝ)
def noisyMeanDeriv (θ x : ℝ) : ℝ :=
  (1 / 2) * noisyProduct θ x ^ (-1 / 2 : ℝ) * noisyProductDeriv θ x
def noisyMeanDeriv2 (θ x : ℝ) : ℝ :=
  -(θ ^ 2) / 4 * noisyProduct θ x ^ (-3 / 2 : ℝ)

lemma hasDerivAt_noisyProduct (θ x : ℝ) :
    HasDerivAt (noisyProduct θ) (noisyProductDeriv θ x) x := by
  have h1 := (((hasDerivAt_id x).const_mul (1 + θ)).add_const (1 - θ)).div_const 2
  have h2 := (((hasDerivAt_id x).const_mul (1 - θ)).add_const (1 + θ)).div_const 2
  convert h1.mul h2 using 1 <;> try rfl
  dsimp [noisyProductDeriv]
  ring

lemma hasDerivAt_noisyProductDeriv (θ x : ℝ) :
    HasDerivAt (noisyProductDeriv θ) ((1 - θ ^ 2) / 2) x := by
  convert (((hasDerivAt_id x).const_mul (1 - θ ^ 2)).add_const (1 + θ ^ 2)).div_const 2 using 1 <;> try rfl
  ring

lemma hasDerivAt_noisyMean {θ x : ℝ} (hQ : 0 < noisyProduct θ x) :
    HasDerivAt (noisyMean θ) (noisyMeanDeriv θ x) x := by
  have hd := (hasDerivAt_noisyProduct θ x).rpow_const (p := (1 / 2 : ℝ)) (Or.inl hQ.ne')
  convert hd using 1 <;> try rfl
  dsimp [noisyMeanDeriv]
  rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by ring]
  ring

lemma hasDerivAt_noisyMeanDeriv {θ x : ℝ} (hQ : 0 < noisyProduct θ x) :
    HasDerivAt (noisyMeanDeriv θ) (noisyMeanDeriv2 θ x) x := by
  have hd := (((hasDerivAt_noisyProduct θ x).rpow_const (p := (-1 / 2 : ℝ)) (Or.inl hQ.ne')).const_mul
    (1 / 2 : ℝ)).mul (hasDerivAt_noisyProductDeriv θ x)
  have hQpow : noisyProduct θ x ^ (-1 / 2 : ℝ) =
      noisyProduct θ x ^ (-3 / 2 : ℝ) * noisyProduct θ x := by
    rw [show (-1 / 2 : ℝ) = -3 / 2 + 1 by ring, Real.rpow_add hQ, Real.rpow_one]
  convert hd using 1 <;> try rfl
  dsimp [noisyMeanDeriv2]
  rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by ring, hQpow]
  dsimp [noisyProductDeriv, noisyProduct]
  ring

/-- The actual normalized two-point power-mean inequality, proved by the
curvature comparison and tangency at x=1. -/
theorem normalized_two_point {r θ x : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hθr : θ ≤ 1 - r) (hx : 0 < x) :
    powerMean r x ≤ noisyMean θ x := by
  let D : ℝ → ℝ := fun y => noisyMean θ y - powerMean r y
  let D1 : ℝ → ℝ := fun y => noisyMeanDeriv θ y - powerMeanDeriv r y
  let D2 : ℝ → ℝ := fun y => noisyMeanDeriv2 θ y - powerMeanDeriv2 r y
  have hθ1 : θ ≤ 1 := by linarith
  have hQ : ∀ y : ℝ, 0 < y → 0 < noisyProduct θ y := fun y hy =>
    hy.trans_le (noisyProduct_ge_input hθ hθ1)
  have hd : ∀ y : ℝ, 0 < y → HasDerivAt D (D1 y) y := fun y hy =>
    (hasDerivAt_noisyMean (hQ y hy)).sub (hasDerivAt_powerMean hr.ne' hy)
  have hd1 : ∀ y : ℝ, 0 < y → HasDerivAt D1 (D2 y) y := fun y hy =>
    (hasDerivAt_noisyMeanDeriv (hQ y hy)).sub (hasDerivAt_powerMeanDeriv hr.ne' hy)
  have hpos : ∀ y : ℝ, 0 < y → 0 ≤ D2 y := by
    intro y hy
    have h := curvature_comparison hr hr1 hθ hθr hy
    dsimp [D2, noisyMeanDeriv2, powerMeanDeriv2]
    nlinarith
  have hconv : ConvexOn ℝ (Ioi 0) D := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (f' := D1) (f'' := D2)
    · intro y hy
      exact (hd y (by simpa using hy)).hasDerivWithinAt
    · intro y hy
      exact (hd1 y (by simpa using hy)).hasDerivWithinAt
    · intro y hy
      exact hpos y (by simpa using hy)
  have hQ1 : noisyProduct θ 1 = 1 := by dsimp [noisyProduct]; ring
  have hD1 : D1 1 = 0 := by
    dsimp [D1, noisyMeanDeriv, powerMeanDeriv]
    rw [hQ1]
    simp only [Real.one_rpow]
    dsimp [noisyProductDeriv]
    ring_nf
    norm_num
  have hmin := hconv.isMinOn_of_rightDeriv_eq_zero (show (1 : ℝ) ∈ interior (Ioi 0) by simp)
    ((hd 1 (by norm_num)).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 1) |>.trans hD1)
  have h := hmin hx
  have hD0 : D 1 = 0 := by
    dsimp [D, noisyMean, powerMean]
    rw [hQ1]
    norm_num
  rw [hD0] at h
  dsimp [D] at h
  linarith

/-- The two-point real power mean of positive inputs is positive. -/
theorem two_point_powerMean_pos {r a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < ((a ^ r + b ^ r) / 2) ^ (1 / r) := by
  exact Real.rpow_pos_of_pos (by positivity) _

/-- Homogeneity turns the normalized analytic inequality into the two-point
squared-mean estimate needed for the bilinear transfer. -/
theorem homogeneous_two_point_sq {r a b : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 < a) (hb : 0 < b) :
    (((a ^ r + b ^ r) / 2) ^ (1 / r)) ^ 2 ≤
      ((a + b) / 2) ^ 2 - ((1 - r) * (a - b) / 2) ^ 2 := by
  have hx : 0 < a / b := div_pos ha hb
  have hθ : 0 ≤ 1 - r := by linarith
  have hθ1 : 1 - r ≤ 1 := by linarith
  have hQ : 0 < noisyProduct (1 - r) (a / b) :=
    hx.trans_le (noisyProduct_ge_input hθ hθ1)
  have h := normalized_two_point hr hr1 hθ (le_refl (1 - r)) hx
  have hmnonneg : 0 ≤ powerMean r (a / b) :=
    Real.rpow_nonneg (base_pos hx).le _
  have hs := mul_self_le_mul_self hmnonneg h
  have hnoisy : noisyMean (1 - r) (a / b) * noisyMean (1 - r) (a / b) =
      noisyProduct (1 - r) (a / b) := by
    dsimp [noisyMean]
    rw [← Real.rpow_add hQ]
    norm_num
  rw [hnoisy] at hs
  have hbpow : 0 < b ^ r := Real.rpow_pos_of_pos hb r
  have havg : ((a / b) ^ r + 1) / 2 = ((a ^ r + b ^ r) / 2) / b ^ r := by
    rw [Real.div_rpow ha.le hb.le]
    field_simp
  have hscale : powerMean r (a / b) * b = ((a ^ r + b ^ r) / 2) ^ (1 / r) := by
    dsimp [powerMean]
    rw [havg, Real.div_rpow (by positivity) hbpow.le, ← Real.rpow_mul hb.le]
    rw [show r * (1 / r) = 1 by field_simp, Real.rpow_one]
    exact div_mul_cancel₀ _ hb.ne'
  calc
    (((a ^ r + b ^ r) / 2) ^ (1 / r)) ^ 2 = (powerMean r (a / b) * b) ^ 2 := by rw [hscale]
    _ = (powerMean r (a / b) * powerMean r (a / b)) * b ^ 2 := by ring
    _ ≤ noisyProduct (1 - r) (a / b) * b ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg b)
    _ = ((a + b) / 2) ^ 2 - ((1 - r) * (a - b) / 2) ^ 2 := by
      dsimp [noisyProduct]
      field_simp
      ring

end SpinGlass.ReverseHypercontractivityTwoPoint
