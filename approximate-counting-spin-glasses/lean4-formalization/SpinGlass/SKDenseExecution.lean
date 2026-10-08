import SpinGlass.SKPrimitiveExpansion

/-!
# Point-update execution of dense coefficient multiplication

The mathematical coefficient convolution is executed by one pass over ordered
basis pairs. A surviving pair computes one scalar product and changes one target
register. Thus the algorithm does not recompute the full convolution separately
for each output coordinate.
-/

noncomputable section
namespace SpinGlass.SKDenseExecution

open scoped BigOperators
open SKCoefficient

/-- One actual register update for a basis pair. -/
def pushStep {b L : ℕ} (f g : Coefficients b L) (p : Basis b L × Basis b L)
    (acc : Coefficients b L) : Coefficients b L :=
  match basisMul p.1 p.2 with
  | none => acc
  | some z => Function.update acc z (acc z + f p.1 * g p.2)

/-- Every update is precisely its single-coordinate contribution. -/
theorem pushStep_eq {b L : ℕ} (f g : Coefficients b L) (p : Basis b L × Basis b L)
    (acc : Coefficients b L) :
    pushStep f g p acc = acc + fun z => pairContribution p.1 p.2 z (f p.1) (g p.2) := by
  funext z
  cases h : basisMul p.1 p.2 with
  | none => simp [pushStep, h, pairContribution]
  | some x =>
    by_cases hz : x = z
    · subst z
      simp [pushStep, h, pairContribution]
    · have hzx : z ≠ x := Ne.symm hz
      simp [pushStep, h, pairContribution, hz, hzx, Function.update_of_ne]

/-- Sequential in-place pair traversal, with the current coefficient registers explicit. -/
def pushLoop {b L : ℕ} (f g : Coefficients b L) :
    List (Basis b L × Basis b L) → Coefficients b L → Coefficients b L
  | [], acc => acc
  | p :: ps, acc => pushLoop f g ps (pushStep f g p acc)

/-- Loop invariant for an arbitrary list of scheduled basis pairs. -/
theorem pushLoop_correct {b L : ℕ} (f g : Coefficients b L)
    (ps : List (Basis b L × Basis b L)) (acc : Coefficients b L) :
    pushLoop f g ps acc = acc +
      (ps.map (fun p => fun z => pairContribution p.1 p.2 z (f p.1) (g p.2))).sum := by
  induction ps generalizing acc with
  | nil => simp [pushLoop]
  | cons p ps ih =>
    rw [pushLoop, ih, pushStep_eq]
    simp only [List.map_cons, List.sum_cons]
    exact add_assoc _ _ _

/-- The scheduled multiplication visits each ordered basis pair once. -/
def denseMul {b L : ℕ} (f g : Coefficients b L) : Coefficients b L :=
  pushLoop f g (Finset.univ : Finset (Basis b L × Basis b L)).toList 0

/-- The point-update implementation computes the mathematical dense convolution. -/
theorem denseMul_correct {b L : ℕ} (f g : Coefficients b L) : denseMul f g = mul f g := by
  rw [denseMul, pushLoop_correct, zero_add]
  rw [Finset.sum_map_toList]
  funext z
  rw [Finset.sum_apply]
  simp only [mul, Fintype.sum_prod_type]

/-- Scalar arithmetic performed at a single pair: one multiply and one add if accepted. -/
def stepArithmetic {b L : ℕ} (p : Basis b L × Basis b L) : ℕ :=
  if compatible p.1 p.2 then 2 else 0

/-- Arithmetic count for the actual sequential pair schedule. -/
def loopArithmetic {b L : ℕ} : List (Basis b L × Basis b L) → ℕ
  | [] => 0
  | p :: ps => stepArithmetic p + loopArithmetic ps

theorem loopArithmetic_le {b L : ℕ} (ps : List (Basis b L × Basis b L)) :
    loopArithmetic ps ≤ 2 * ps.length := by
  induction ps with
  | nil => simp [loopArithmetic]
  | cons p ps ih =>
    have hp : stepArithmetic p ≤ 2 := by unfold stepArithmetic; split <;> omega
    simp only [loopArithmetic, List.length_cons]
    omega

/-- Exact basis-pair schedule size and a concrete arithmetic bound. -/
theorem denseMul_arithmetic_bound (b L : ℕ) :
    loopArithmetic (Finset.univ : Finset (Basis b L × Basis b L)).toList ≤
      2 * (L + 1) ^ 2 * 4 ^ L * 36 ^ b := by
  have h := loopArithmetic_le (Finset.univ : Finset (Basis b L × Basis b L)).toList
  simp only [Finset.length_toList, Finset.card_univ, card_multiplication_pairs] at h
  simpa only [Nat.mul_assoc] using h

/-- Algorithm 5's exponential loop, using the actual point-update multiplication. -/
def expExecution {b L : ℕ} (f : Coefficients b L) : ℕ → Coefficients b L × Coefficients b L
  | 0 => (one b L, one b L)
  | n + 1 =>
      let old := expExecution f n
      let next := scale (((n + 1 : ℕ) : ℝ)⁻¹) (denseMul old.1 f)
      (next, old.2 + next)

theorem expExecution_correct {b L : ℕ} (f : Coefficients b L) (n : ℕ) :
    expExecution f n = SKExponential.expLoop f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expExecution, SKExponential.expLoop, ih, denseMul_correct]

/-- The direct-edge factor loop with the same scheduled multiplication. -/
def directExecution {b L : ℕ} : List (Coefficients b L) → Coefficients b L → Coefficients b L
  | [], acc => acc
  | e :: es, acc => directExecution es (denseMul acc (one b L + e))

theorem directExecution_correct {b L : ℕ} (es : List (Coefficients b L))
    (acc : Coefficients b L) :
    directExecution es acc = SKExponential.directLoop es acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih => simp only [directExecution, SKExponential.directLoop, ih, denseMul_correct]

/-- Concrete point-update algebra evaluator used after primitive construction. -/
def evaluator {b L : ℕ} (primitives : Coefficients b L)
    (edges : List (Coefficients b L)) : Coefficients b L :=
  directExecution edges (expExecution primitives L).2

theorem evaluator_correct {b L : ℕ} (primitives : Coefficients b L)
    (edges : List (Coefficients b L)) :
    evaluator primitives edges = SKExponential.algebraEvaluator primitives edges := by
  rw [evaluator, expExecution_correct, directExecution_correct]
  rfl

end SpinGlass.SKDenseExecution
