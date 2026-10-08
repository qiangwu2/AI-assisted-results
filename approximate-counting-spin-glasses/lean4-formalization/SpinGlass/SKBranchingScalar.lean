import SpinGlass.SupportScalar
import SpinGlass.CutoffTail
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact scalar reduction of the Gaussian pairing bound to the SK constants. -/

noncomputable section
namespace SpinGlass.SKBranchingScalar
open Nat Real
open scoped Nat

def massConstant (B : ℝ) : ℝ := (1-B^2)^(-(1/2 : ℝ))
def branchConstant (B : ℝ) : ℝ := 2 * Real.exp 1 * B^4 / (3*(1-B^2)^2)

theorem odd_doubleFactorial_le (m : ℕ) : (2*m-1)‼ ≤ (2*m)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 2*(m+1)-1 = 2*m+1 by omega, Nat.doubleFactorial_add_one]
    calc
      (2*m+1)*(2*m-1)‼ ≤ (2*(m+1))*(2*(m+1))^m :=
        Nat.mul_le_mul (by omega) (ih.trans (Nat.pow_le_pow_left (by omega) _))
      _ = _ := by rw [pow_succ]; ring

theorem four_doubleFactorial_le (b : ℕ) : ((4*b-1)‼ : ℝ) ≤ (4*(b:ℝ))^(2*b) := by
  have h := odd_doubleFactorial_le (2*b)
  rw [show 2*(2*b)=4*b by omega] at h
  exact_mod_cast h

theorem tilt_power_eq {d : ℝ} (hd : 0 < d) (b : ℕ) :
    d ^ (-((2*b : ℕ) : ℝ)-1/2) = d^(-(1/2 : ℝ)) / d^(2*b) := by
  rw [show -((2*b : ℕ) : ℝ)-1/2 = -(1/2 : ℝ) + -((2*b : ℕ) : ℝ) by ring,
    Real.rpow_add hd]
  simp only [Real.rpow_neg hd.le, Real.rpow_natCast, div_eq_mul_inv]

theorem reduced_bound_identity {N b : ℕ} (hN : 0 < N) (hb : 0 < b) {B : ℝ}
    (hden : 0 < 1-B^2) :
    (Real.exp 1 * N / b)^b *
      ((B^2/(N:ℝ))^(2*b) / 24^b * (4*(b:ℝ))^(2*b) *
        (1-B^2)^(-((2*b : ℕ):ℝ)-1/2)) =
      massConstant B * (branchConstant B * b / N)^b := by
  have hNne : (N:ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hbne : (b:ℝ) ≠ 0 := (Nat.cast_pos.mpr hb).ne'
  rw [tilt_power_eq hden]
  simp only [pow_mul, div_pow, mul_pow, massConstant, branchConstant]
  have hBpow : (B^2)^2 = B^4 := by ring
  have hbpow : (4*(b:ℝ))^2 = 16*(b:ℝ)^2 := by ring
  simp only [hBpow]
  have hnum : (3:ℝ)^b*16^b = (2:ℝ)^b*24^b := by rw [← mul_pow, ← mul_pow]; norm_num
  field_simp
  linear_combination ((N:ℝ)^(2*b)*B^(4*b)*(b:ℝ)^(2*b))*hnum

/-- The precise `C_B (A_B b/N)^b` conversion, including arbitrary second
moment coefficients below the physical `B²/N` bound. -/
theorem gaussian_bound_to_branch_bound {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
    {B r : ℝ} (hB : 0 ≤ B) (hB1 : B < 1) (hr : 0 ≤ r) (hrB : r ≤ B^2/(N:ℝ)) :
    (N.choose b : ℝ) * (r^(2*b)/24^b * ((4*b-1)‼:ℝ) *
      (1-(N:ℝ)*r)^(-((2*b : ℕ):ℝ)-1/2)) ≤
      massConstant B * (branchConstant B * b / N)^b := by
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hden : 0 < 1-B^2 := by nlinarith
  have hNr : (N:ℝ)*r ≤ B^2 := by
    have h := (le_div_iff₀ hNR).mp hrB
    nlinarith
  have hdenr : 0 ≤ 1-(N:ℝ)*r := by linarith
  have htilt : (1-(N:ℝ)*r)^(-((2*b : ℕ):ℝ)-1/2) ≤
      (1-B^2)^(-((2*b : ℕ):ℝ)-1/2) := by
    exact Real.rpow_le_rpow_of_nonpos hden (by linarith)
      (by have hn := (Nat.cast_nonneg (2*b) : (0:ℝ) ≤ (2*b:ℕ)); linarith)
  rw [← reduced_bound_identity hN hb hden]
  apply mul_le_mul
  · exact SpinGlass.SupportScalar.binomial_upper_bound N b
  · apply mul_le_mul
    · exact mul_le_mul
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hr hrB _) (by positivity))
        (four_doubleFactorial_le b) (by positivity) (by positivity)
    · exact htilt
    · positivity
    · positivity
  · positivity
  · positivity

theorem zero_branch_bound {N : ℕ} (hN : 0 < N) {B r : ℝ}
    (hB : 0 ≤ B) (hB1 : B < 1) (hr : 0 ≤ r) (hrB : r ≤ B^2/(N:ℝ)) :
    (N.choose 0 : ℝ) * (r^(2*0)/24^0 * ((4*0-1)‼:ℝ) *
      (1-(N:ℝ)*r)^(-((2*0 : ℕ):ℝ)-1/2)) ≤ massConstant B := by
  norm_num
  apply Real.rpow_le_rpow_of_nonpos (by nlinarith : 0 < 1-B^2)
  · have h := (le_div_iff₀ (Nat.cast_pos.mpr hN : (0:ℝ)<N)).mp hrB
    nlinarith
  · norm_num

theorem massConstant_ge_one {B : ℝ} (hB : 0 ≤ B) (hB1 : B < 1) : 1 ≤ massConstant B := by
  have hd : 0 < 1-B^2 := by nlinarith
  have h := Real.rpow_le_rpow_of_nonpos hd (show 1-B^2 ≤ 1 by nlinarith) (by norm_num : -(1/2:ℝ) ≤ 0)
  simpa only [Real.one_rpow, massConstant] using h

theorem branchConstant_nonneg (B : ℝ) : 0 ≤ branchConstant B := by
  unfold branchConstant
  positivity

theorem branch_power_le_exp {N b : ℕ} (hN : 0 < N) (hb : 0 < b) (B : ℝ) :
    (branchConstant B * b / N)^b ≤
      Real.exp (-SpinGlass.CutoffTail.phi 1 (max 1 (branchConstant B)) N b) := by
  let a := max 1 (branchConstant B)
  have ha : 0 < a := zero_lt_one.trans_le (le_max_left _ _)
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hbR : 0 < (b:ℝ) := Nat.cast_pos.mpr hb
  have hab : 0 < a*b/(N:ℝ) := by positivity
  have heq : (a*b/(N:ℝ))^b = Real.exp (-SpinGlass.CutoffTail.phi 1 a N b) := by
    rw [← Real.exp_log (pow_pos hab _), Real.log_pow]
    have hlog : Real.log ((N:ℝ)/(a*b)) = -Real.log (a*b/(N:ℝ)) := by
      rw [Real.log_div hNR.ne' (mul_pos ha hbR).ne', Real.log_div (mul_pos ha hbR).ne' hNR.ne']
      ring
    congr 1
    simp only [SpinGlass.CutoffTail.phi, one_mul, hlog]
    ring
  rw [← heq]
  apply pow_le_pow_left₀ (div_nonneg (mul_nonneg (branchConstant_nonneg B) hbR.le) hNR.le)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hbR.le) hNR.le

end SpinGlass.SKBranchingScalar
