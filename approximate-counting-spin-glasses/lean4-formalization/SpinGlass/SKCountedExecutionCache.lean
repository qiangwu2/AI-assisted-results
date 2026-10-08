import SpinGlass.SKCountedExecutionCore
import SpinGlass.SKFastEvaluator
import SpinGlass.SKOperationCount

/-! All memo tables are computed once per branch or outside root and reused by
 every primitive closure. The counted closures read only this saved cache. -/
noncomputable section
namespace SpinGlass.SKCountedExecution
open scoped BigOperators
open SpinGlass.ArithmeticEvaluation SpinGlass.SKFastEvaluator
variable {V W : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]

abbrev Root (W : Type*) (b : ℕ) := Fin b ⊕ W

def rootStart {b : ℕ} (branch : Fin b → V) (outside : W → V)
    (f : Finset V → ℝ) : Root W b → W → ℝ
  | Sum.inl a => fun i => pairWeight f (branch a) (outside i)
  | Sum.inr r => SpinGlass.ColorCycleChain.rootStart r

/-- Exactly b+|W| separate memo runs are tabulated once and saved. -/
def rootCache {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) : Counted (Root W b → Table W L) :=
  tabulate (fun root => memo χ (rootStart branch outside f root)
    (fun i j => pairWeight f (outside i) (outside j)) L)

@[simp] theorem rootCache_value {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (root : Root W b) :
    (rootCache branch outside χ f).value root =
      SpinGlass.ColorMemoExecution.memo χ (rootStart branch outside f root)
        (fun i j => pairWeight f (outside i) (outside j)) L := by
  rw [rootCache, tabulate_value, memo_value]

/-- The shared table-cache execution has exactly the profile's table upper bound. -/
theorem rootCache_operations_le {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) :
    (rootCache branch outside χ f).operations ≤
      SpinGlass.SKOperationCount.tableWork (Fintype.card W) b L := by
  rw [rootCache, tabulate_operations]
  calc
    _ ≤ ∑ _root : Root W b, L * (2 * 2 ^ L * (Fintype.card W) ^ 2) :=
      Finset.sum_le_sum (fun root _ => memo_operations_le _ _ _ L)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Root, Fintype.card_sum,
        Fintype.card_fin, SpinGlass.SKOperationCount.tableWork, Nat.cast_id]
      ring

/-- Endpoint closure from a saved branch-root table; no memo program occurs here. -/
def cachedPath {b L : ℕ} (branch : Fin b → V) (outside : W → V) (f : Finset V → ℝ)
    (cache : Root W b → Table W L) (a c : Fin b) (S : Finset (Fin L)) : Computation :=
  sumFinset Finset.univ (fun j =>
    mul (literal (cache (Sum.inl a) S j)) (literal (pairWeight f (outside j) (branch c))))

@[simp] theorem cachedPath_operations {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (f : Finset V → ℝ) (cache : Root W b → Table W L) (a c : Fin b) (S : Finset (Fin L)) :
    (cachedPath branch outside f cache a c S).operations = 2 * Fintype.card W := by
  simp [cachedPath, sumFinset_operations, mul, literal]; omega

theorem cachedPath_value {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (a c : Fin b) (S : Finset (Fin L)) :
    (cachedPath branch outside f (rootCache branch outside χ f).value a c S).value =
      pathCoefficient branch outside χ f a c S := by
  simp [cachedPath, mul, literal, pathCoefficient, memoClosure, rootStart]

/-- Rooted-cycle normalization uses the same saved branch-root table. -/
def cachedReturn {b L : ℕ} (branch : Fin b → V) (outside : W → V) (f : Finset V → ℝ)
    (cache : Root W b → Table W L) (a : Fin b) (S : Finset (Fin L)) : Computation :=
  if 2 ≤ S.card then mul (literal (2 : ℝ)⁻¹) (cachedPath branch outside f cache a a S) else literal 0

theorem cachedReturn_operations_le {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (f : Finset V → ℝ) (cache : Root W b → Table W L) (a : Fin b) (S : Finset (Fin L)) :
    (cachedReturn branch outside f cache a S).operations ≤ 2 * Fintype.card W + 1 := by
  unfold cachedReturn
  split_ifs <;> simp [mul, literal]

theorem cachedReturn_value {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (a : Fin b) (S : Finset (Fin L)) :
    (cachedReturn branch outside f (rootCache branch outside χ f).value a S).value =
      returnCoefficient branch outside χ f a S := by
  unfold cachedReturn returnCoefficient
  split_ifs <;> simp [mul, literal, cachedPath_value]

/-- A flat root/endpoint sum avoids recomputing or repeatedly summing stored
memo entries when forming an entirely outside cycle. -/
def cachedCycle {b L : ℕ} (outside : W → V) (f : Finset V → ℝ)
    (cache : Root W b → Table W L) (S : Finset (Fin L)) : Computation :=
  if 3 ≤ S.card then
    mul (literal (2 * S.card : ℝ)⁻¹)
      (sumFinset (Finset.univ : Finset (W × W)) (fun p =>
        mul (literal (cache (Sum.inr p.1) S p.2)) (literal (pairWeight f (outside p.2) (outside p.1)))))
  else literal 0

theorem cachedCycle_operations_le {b L : ℕ} (outside : W → V) (f : Finset V → ℝ)
    (cache : Root W b → Table W L) (S : Finset (Fin L)) :
    (cachedCycle outside f cache S).operations ≤ 2 * (Fintype.card W) ^ 2 + 1 := by
  unfold cachedCycle
  split_ifs
  · simp [mul, literal, sumFinset_operations, Fintype.card_prod]
    nlinarith
  · simp [literal]

theorem cachedCycle_value {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (S : Finset (Fin L)) :
    (cachedCycle outside f (rootCache branch outside χ f).value S).value =
      cycleCoefficient outside χ f S := by
  unfold cachedCycle cycleCoefficient
  split_ifs
  · simp [mul, literal, Fintype.sum_prod_type, memoClosure, rootStart]
  · rfl

end SpinGlass.SKCountedExecution
