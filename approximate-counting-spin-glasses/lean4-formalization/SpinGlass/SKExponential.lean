import SpinGlass.SKCoefficient
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The exact finite-exponential loop in the SK algorithm

The loop is stated for the concrete dense coefficient operations proved in
`SKCoefficient`. Its running state, factorial denominators, and final finite sum
are all explicit. No analytic exponential or approximation is involved.
-/

noncomputable section

namespace SpinGlass.SKExponential

open scoped BigOperators
open SKCoefficient

/-- The `n`th term in the finite exponential, with coefficient-field division. -/
def term {b L : ℕ} (f : Coefficients b L) (n : ℕ) : Coefficients b L :=
  scale ((n.factorial : ℝ)⁻¹) (pow f n)

@[simp] theorem term_zero {b L : ℕ} (f : Coefficients b L) : term f 0 = one b L := by
  simp [term, pow]

/-- Multiplying the current term and dividing by the new index gives the next term. -/
theorem term_step {b L : ℕ} (f : Coefficients b L) (n : ℕ) :
    scale (((n + 1 : ℕ) : ℝ)⁻¹) (mul (term f n) f) = term f (n + 1) := by
  simp only [term, scale_mul, scale_scale, pow, Nat.factorial_succ, Nat.cast_mul,
    mul_inv_rev]
  rw [_root_.mul_comm]

/-- The actual pair of arrays `(V,E)` updated in Algorithm 5, lines 4--7. -/
def expLoop {b L : ℕ} (f : Coefficients b L) : ℕ → Coefficients b L × Coefficients b L
  | 0 => (one b L, one b L)
  | n + 1 =>
      let old := expLoop f n
      let next := scale (((n + 1 : ℕ) : ℝ)⁻¹) (mul old.1 f)
      (next, old.2 + next)

/-- Both loop registers have their exact algebraic values after every iteration. -/
theorem expLoop_invariant {b L : ℕ} (f : Coefficients b L) (n : ℕ) :
    (expLoop f n).1 = term f n ∧
      (expLoop f n).2 = ∑ j ∈ Finset.range (n + 1), term f j := by
  induction n with
  | zero => simp [expLoop]
  | succ n ih =>
    simp only [expLoop]
    rw [ih.1, term_step, ih.2]
    constructor
    · rfl
    · exact (Finset.sum_range_succ (fun j => term f j) (n + 1)).symm

/-- Algorithm 5 computes the precise polynomial (74), for arbitrary signed arrays. -/
theorem expLoop_correct {b L : ℕ} (f : Coefficients b L) :
    (expLoop f L).2 = ∑ j ∈ Finset.range (L + 1),
      scale ((j.factorial : ℝ)⁻¹) (pow f j) :=
  (expLoop_invariant f L).2

/-- All powers above the number of colors vanish for color-consuming arrays. -/
theorem pow_eq_zero_above_colors {b L : ℕ} (f : Coefficients b L)
    (hf : VanishesBelow 1 f) {n : ℕ} (hn : L < n) : pow f n = 0 := by
  funext z
  have hcard : z.2.1.card ≤ L := by simpa using Finset.card_le_univ z.2.1
  exact vanishesBelow_pow f hf n z (by omega)

/-- Omitted terms are identically zero, rather than a truncation error. -/
theorem term_eq_zero_above_colors {b L : ℕ} (f : Coefficients b L)
    (hf : VanishesBelow 1 f) {n : ℕ} (hn : L < n) : term f n = 0 := by
  rw [term, pow_eq_zero_above_colors f hf hn]
  funext z
  simp [scale]

/-- Running the exponential loop past `L` cannot change the result. -/
theorem expLoop_stable {b L : ℕ} (f : Coefficients b L)
    (hf : VanishesBelow 1 f) (k : ℕ) :
    (expLoop f (L + k)).2 = (expLoop f L).2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hn : L < L + k + 1 := by omega
    have hv := (expLoop_invariant f (L + k)).1
    change (expLoop f (L + k)).2 +
      scale (((L + k + 1 : ℕ) : ℝ)⁻¹) (mul (expLoop f (L + k)).1 f) = _
    rw [hv, term_step, term_eq_zero_above_colors f hf hn]
    simpa using ih

/-- Multiplication work in the loop, measured in basis-pair visits. -/
def expPairVisits (b L : ℕ) : ℕ := L * Fintype.card (Basis b L × Basis b L)

theorem expPairVisits_exact (b L : ℕ) :
    expPairVisits b L = L * (L + 1) ^ 2 * 4 ^ L * 36 ^ b := by
  rw [expPairVisits, card_multiplication_pairs]
  ring

/-- A list of direct-edge factors is multiplied into an existing array. -/
def directLoop {b L : ℕ} : List (Coefficients b L) → Coefficients b L → Coefficients b L
  | [], acc => acc
  | edge :: edges, acc => directLoop edges (mul acc (one b L + edge))

/-- The product of direct-edge factors, with each supplied factor used once. -/
def directProduct {b L : ℕ} : List (Coefficients b L) → Coefficients b L
  | [] => one b L
  | edge :: edges => mul (one b L + edge) (directProduct edges)

/-- Lines 8--10 multiply precisely the supplied direct-edge factors. -/
theorem directLoop_correct {b L : ℕ} (edges : List (Coefficients b L))
    (acc : Coefficients b L) : directLoop edges acc = mul acc (directProduct edges) := by
  induction edges generalizing acc with
  | nil => simp [directLoop, directProduct]
  | cons edge edges ih =>
    rw [directLoop, ih, directProduct, SKCoefficient.mul_assoc]

/-- The whole algebraic portion of Algorithm 5 is an explicit implementation. -/
def algebraEvaluator {b L : ℕ} (primitives : Coefficients b L)
    (directEdges : List (Coefficients b L)) : Coefficients b L :=
  directLoop directEdges (expLoop primitives L).2

theorem algebraEvaluator_correct {b L : ℕ} (primitives : Coefficients b L)
    (directEdges : List (Coefficients b L)) :
    algebraEvaluator primitives directEdges =
      mul (∑ j ∈ Finset.range (L + 1), term primitives j) (directProduct directEdges) := by
  rw [algebraEvaluator, directLoop_correct, (expLoop_invariant primitives L).2]

end SpinGlass.SKExponential
