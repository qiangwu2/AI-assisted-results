import SpinGlass.Expansion
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exact finite coloring probabilities

The probability is computed from all functions into the palette, and the
colorful event is actual injectivity. Falling factorials and the exponential
lower bound are proved, rather than assumed as a coloring guarantee.
-/

noncomputable section

namespace SpinGlass.ColoringProbability

open scoped BigOperators

/-- The probability written in (18). -/
def probability (L m : ℕ) : ℝ := (L.descFactorial m : ℝ) / (L : ℝ) ^ m

/-- Uniform averaging over an arbitrary finite sample space. -/
def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω

/-- The actual indicator of an injective coloring. -/
def indicator {V : Type*} [Fintype V] (L : ℕ) (χ : V → Fin L) : ℝ :=
  if Function.Injective χ then 1 else 0

private def injectiveEquivEmbedding {V : Type*} [Fintype V] (L : ℕ) :
    {χ : V → Fin L // Function.Injective χ} ≃ (V ↪ Fin L) where
  toFun χ := ⟨χ.val, χ.property⟩
  invFun χ := ⟨χ, χ.injective⟩
  left_inv χ := rfl
  right_inv χ := rfl

/-- Counting actual injective colorings gives the descending factorial. -/
theorem card_injective_colorings {V : Type*} [Fintype V] [DecidableEq V] (L : ℕ) :
    Fintype.card {χ : V → Fin L // Function.Injective χ} =
      L.descFactorial (Fintype.card V) := by
  rw [Fintype.card_congr (injectiveEquivEmbedding (V := V) L), Fintype.card_embedding_eq]
  simp

/-- Independent uniform colors have precisely the paper's colorful probability. -/
theorem mean_indicator {V : Type*} [Fintype V] [DecidableEq V] (L : ℕ) :
    mean (indicator (V := V) L) = probability L (Fintype.card V) := by
  classical
  unfold mean indicator
  rw [Finset.sum_boole, ← Fintype.card_subtype (fun χ : V → Fin L => Function.Injective χ),
    card_injective_colorings]
  simp [probability, Fintype.card_fun, div_eq_mul_inv, mul_comm]

@[simp] theorem probability_zero (L : ℕ) : probability L 0 = 1 := by
  simp [probability]

theorem probability_nonneg (L m : ℕ) : 0 ≤ probability L m := by
  unfold probability
  positivity

theorem probability_pos {L m : ℕ} (hL : 0 < L) (hm : m ≤ L) : 0 < probability L m := by
  apply div_pos
  · exact_mod_cast Nat.descFactorial_pos.mpr hm
  · positivity

theorem probability_le_one {L m : ℕ} (hL : 0 < L) : probability L m ≤ 1 := by
  unfold probability
  apply (div_le_one (by positivity : (0 : ℝ) < (L : ℝ) ^ m)).mpr
  exact_mod_cast Nat.descFactorial_le_pow L m

/-- Adding a vertex multiplies its success probability by the unused palette fraction. -/
theorem probability_succ {L : ℕ} (hL : 0 < L) (m : ℕ) :
    probability L (m + 1) = ((L - m : ℕ) : ℝ) / (L : ℝ) * probability L m := by
  have hLn : (L : ℝ) ≠ 0 := by positivity
  unfold probability
  rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
  field_simp

/-- Colorfulness becomes less likely as more vertices are colored. -/
theorem probability_antitone {L : ℕ} (hL : 0 < L) : Antitone (probability L) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [probability_succ hL]
  have hp := probability_nonneg L m
  have hr : ((L - m : ℕ) : ℝ) / (L : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < L)).mpr
    exact_mod_cast Nat.sub_le L m
  nlinarith

/-- The all-colors probability is the familiar factorial ratio. -/
theorem probability_self (L : ℕ) : probability L L = (L.factorial : ℝ) / (L : ℝ) ^ L := by
  simp [probability, Nat.descFactorial_self]

/-- The exponential lower bound follows directly from a term of the exponential series. -/
theorem exp_neg_le_probability_self {L : ℕ} (hL : 0 < L) :
    Real.exp (-(L : ℝ)) ≤ probability L L := by
  rw [probability_self]
  have hp : (0 : ℝ) < (L : ℝ) ^ L := by positivity
  have hf : (0 : ℝ) < L.factorial := by positivity
  have he : (0 : ℝ) < Real.exp (L : ℝ) := Real.exp_pos _
  have hterm := Real.pow_div_factorial_le_exp (L : ℝ) (by positivity) L
  have hmul := (div_le_iff₀ hf).mp hterm
  apply (le_div_iff₀ hp).mpr
  calc
    Real.exp (-(L : ℝ)) * (L : ℝ) ^ L = (L : ℝ) ^ L / Real.exp (L : ℝ) := by
      rw [Real.exp_neg]
      ring
    _ ≤ (L.factorial : ℝ) := (div_le_iff₀ he).mpr (by nlinarith)

/-- The uniform bound (80) for every allowed outside support size. -/
theorem exp_neg_le_probability {L m : ℕ} (hL : 0 < L) (hm : m ≤ L) :
    Real.exp (-(L : ℝ)) ≤ probability L m :=
  le_trans (exp_neg_le_probability_self hL) (probability_antitone hL hm)

/-- The inverse colorful-probability factor used in the variance bound. -/
theorem probability_inv_le_exp {L m : ℕ} (hL : 0 < L) (hm : m ≤ L) :
    (probability L m)⁻¹ ≤ Real.exp (L : ℝ) := by
  have hp := probability_pos hL hm
  have he := exp_neg_le_probability hL hm
  rw [Real.exp_neg] at he
  exact (inv_le_comm₀ hp (Real.exp_pos _)).mpr he

/-- The coefficient assigned to a retained graph in one colorful trial. -/
def coefficient {V : Type*} [Fintype V] (L : ℕ) (χ : V → Fin L) : ℝ :=
  indicator L χ / probability L (Fintype.card V)

/-- The graph coefficient is exactly unbiased for actual independent uniform colors. -/
theorem mean_coefficient {V : Type*} [Fintype V] [DecidableEq V]
    {L : ℕ} (hL : 0 < L) (hm : Fintype.card V ≤ L) :
    mean (coefficient (V := V) L) = 1 := by
  have hp := ne_of_gt (probability_pos hL hm)
  simp only [coefficient, mean, div_eq_mul_inv, ← Finset.sum_mul, ← mul_assoc]
  change mean (indicator (V := V) L) * (probability L (Fintype.card V))⁻¹ = 1
  rw [mean_indicator]
  exact mul_inv_cancel₀ hp

theorem mean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    mean (fun _ : Ω => a) = a := by
  have hk : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hk, ← mul_assoc]

theorem mean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun ω => f ω + g ω) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, mul_add]

theorem mean_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun ω => f ω - g ω) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, mul_sub]

theorem mean_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    mean (fun ω => f ω * a) = mean f * a := by
  simp [mean, ← Finset.sum_mul, mul_assoc]

theorem mean_const_mul {Ω : Type*} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    mean (fun ω => a * f ω) = a * mean f := by
  simp_rw [mul_comm a]
  exact mean_mul_const f a

@[simp] theorem indicator_sq {V : Type*} [Fintype V] (L : ℕ) (χ : V → Fin L) :
    indicator L χ ^ 2 = indicator L χ := by
  unfold indicator
  split <;> norm_num

/-- The exact second moment of the graph coefficient in one trial. -/
theorem mean_coefficient_sq {V : Type*} [Fintype V] [DecidableEq V]
    {L : ℕ} (hL : 0 < L) (hm : Fintype.card V ≤ L) :
    mean (fun χ : V → Fin L => coefficient L χ ^ 2) =
      (probability L (Fintype.card V))⁻¹ := by
  have hp := ne_of_gt (probability_pos hL hm)
  simp only [coefficient, div_eq_mul_inv, mul_pow, indicator_sq]
  rw [mean_mul_const, mean_indicator]
  field_simp

/-- The precise centered variance in (83), before averaging repetitions. -/
theorem mean_coefficient_variance {V : Type*} [Fintype V] [DecidableEq V]
    {L : ℕ} (hL : 0 < L) (hm : Fintype.card V ≤ L) :
    mean (fun χ : V → Fin L => (coefficient L χ - 1) ^ 2) =
      (1 - probability L (Fintype.card V)) / probability L (Fintype.card V) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have hp := ne_of_gt (probability_pos hL hm)
  have hpoint : (fun χ : V → Fin L => (coefficient L χ - 1) ^ 2) =
      (fun χ => coefficient L χ ^ 2 - 2 * coefficient L χ + 1) := by
    funext χ
    ring
  rw [hpoint, mean_add, mean_sub, mean_const_mul, mean_const,
    mean_coefficient_sq hL hm, mean_coefficient hL hm]
  field_simp
  ring

/-- The one-trial signed coefficient error has the claimed exponential bound. -/
theorem mean_coefficient_variance_le_exp {V : Type*} [Fintype V] [DecidableEq V]
    {L : ℕ} (hL : 0 < L) (hm : Fintype.card V ≤ L) :
    mean (fun χ : V → Fin L => (coefficient L χ - 1) ^ 2) ≤ Real.exp (L : ℝ) := by
  rw [mean_coefficient_variance hL hm]
  have hp := probability_pos hL hm
  calc
    (1 - probability L (Fintype.card V)) / probability L (Fintype.card V) ≤
        (probability L (Fintype.card V))⁻¹ := by
      rw [← one_div]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hp)
    _ ≤ Real.exp (L : ℝ) := probability_inv_le_exp hL hm

end SpinGlass.ColoringProbability
