import SpinGlass.SKCountedExecutionCache

/-! Sparse primitive insertion driven by the once-computed root cache. -/
noncomputable section
namespace SpinGlass.SKCountedExecution
open scoped BigOperators
open SpinGlass.ArithmeticEvaluation SpinGlass.SKCoefficient SpinGlass.SKFastEvaluator

structure Instruction (b L : ℕ) where
  target : Option (Basis b L)
  scalar : Computation

def noInstruction (b L : ℕ) : Instruction b L := ⟨none, literal 0⟩

def instructionValue {b L : ℕ} (i : Instruction b L) : Coefficients b L :=
  i.target.elim 0 (fun z => single z i.scalar.value)

@[simp] theorem noInstruction_value (b L : ℕ) : instructionValue (noInstruction b L) = 0 := rfl

def instructionCost {b L : ℕ} (i : Instruction b L) : ℕ :=
  i.target.elim 0 (fun _ => i.scalar.operations + 1)

def sparseStep {b L : ℕ} (i : Instruction b L) (state : Counted (Coefficients b L)) :
    Counted (Coefficients b L) :=
  match i.target with
  | none => state
  | some z => ⟨Function.update state.value z (state.value z + i.scalar.value),
      state.operations + i.scalar.operations + 1⟩

theorem sparseStep_value {b L : ℕ} (i : Instruction b L) (state : Counted (Coefficients b L)) :
    (sparseStep i state).value = state.value + instructionValue i := by
  funext z
  cases h : i.target with
  | none => simp [sparseStep, instructionValue, h]
  | some x =>
    by_cases hx : x = z
    · subst z; simp [sparseStep, instructionValue, h, single]
    · simp [sparseStep, instructionValue, h, single, hx, Ne.symm hx]

theorem sparseStep_operations {b L : ℕ} (i : Instruction b L) (state : Counted (Coefficients b L)) :
    (sparseStep i state).operations = state.operations + instructionCost i := by
  cases h : i.target <;> simp [sparseStep, instructionCost, h, Nat.add_assoc]

def sparseLoop {I : Type*} {b L : ℕ} (program : I → Instruction b L) :
    List I → Counted (Coefficients b L) → Counted (Coefficients b L)
  | [], state => state
  | i :: is, state => sparseLoop program is (sparseStep (program i) state)

theorem sparseLoop_value {I : Type*} {b L : ℕ} (program : I → Instruction b L)
    (is : List I) (state : Counted (Coefficients b L)) :
    (sparseLoop program is state).value = state.value + (is.map (fun i => instructionValue (program i))).sum := by
  induction is generalizing state with
  | nil => simp [sparseLoop]
  | cons i is ih => simp [sparseLoop, ih, sparseStep_value, add_assoc]

theorem sparseLoop_operations {I : Type*} {b L : ℕ} (program : I → Instruction b L)
    (is : List I) (state : Counted (Coefficients b L)) :
    (sparseLoop program is state).operations = state.operations + (is.map (fun i => instructionCost (program i))).sum := by
  induction is generalizing state with
  | nil => simp [sparseLoop]
  | cons i is ih => simp [sparseLoop, ih, sparseStep_operations, Nat.add_assoc]

def assemble {I : Type*} [Fintype I] {b L : ℕ} (program : I → Instruction b L) : Counted (Coefficients b L) :=
  sparseLoop program Finset.univ.toList ⟨0, 0⟩

@[simp] theorem assemble_value {I : Type*} [Fintype I] {b L : ℕ} (program : I → Instruction b L) :
    (assemble program).value = ∑ i, instructionValue (program i) := by simp [assemble, sparseLoop_value]

@[simp] theorem assemble_operations {I : Type*} [Fintype I] {b L : ℕ} (program : I → Instruction b L) :
    (assemble program).operations = ∑ i, instructionCost (program i) := by simp [assemble, sparseLoop_operations]

def insertInstruction {b L : ℕ} (k : ℕ) (S : Finset (Fin L))
    (d : Fin b → CappedDegree) (x : Computation) : Instruction b L :=
  if h : k ≤ L then ⟨some (⟨k, Nat.lt_succ_of_le h⟩, S, d), x⟩ else noInstruction b L

@[simp] theorem insertInstruction_value {b L : ℕ} (k : ℕ) (S : Finset (Fin L))
    (d : Fin b → CappedDegree) (x : Computation) :
    instructionValue (insertInstruction k S d x) = (insertMonomial k S d x.value).coeff := by
  unfold insertInstruction insertMonomial
  split_ifs <;> rfl

theorem insertInstruction_cost_le {b L : ℕ} (k : ℕ) (S : Finset (Fin L))
    (d : Fin b → CappedDegree) (x : Computation) :
    instructionCost (insertInstruction k S d x) ≤ x.operations + 1 := by
  unfold insertInstruction
  split_ifs <;> simp [instructionCost, noInstruction]

abbrev PrimitiveKey (b L : ℕ) :=
  Finset (Fin L) ⊕ ((Fin b × Fin b × Finset (Fin L)) ⊕ (Fin b × Finset (Fin L)))

variable {V W : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]

def primitiveInstruction {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (f : Finset V → ℝ) (cache : Root W b → Table W L) : PrimitiveKey b L → Instruction b L
  | Sum.inl S => if 3 ≤ S.card then insertInstruction S.card S (fun _ => 0)
      (cachedCycle outside f cache S) else noInstruction b L
  | Sum.inr (Sum.inl (a, c, S)) => if a < c ∧ 1 ≤ S.card then
      if S.card + 1 ≤ L then
        insertInstruction (S.card + 1) S (pathDegrees a c)
          (cachedPath branch outside f cache a c S) else noInstruction b L
      else noInstruction b L
  | Sum.inr (Sum.inr (a, S)) => if 2 ≤ S.card then
      if S.card + 1 ≤ L then
        insertInstruction (S.card + 1) S (pathDegrees a a)
          (cachedReturn branch outside f cache a S) else noInstruction b L
      else noInstruction b L

/-- Complete cached primitive construction: only b+|W| memo tables are executed. -/
def primitives {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) : Counted (Coefficients b L) :=
  let cache := rootCache branch outside χ f
  let result := assemble (primitiveInstruction branch outside f cache.value)
  ⟨result.value, cache.operations + result.operations⟩

/-- The sparse point-update program computes precisely the primitive polynomial
used by the mathematical fast evaluator. -/
theorem primitives_value {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) :
    (primitives branch outside χ f).value = (SpinGlass.SKFastEvaluator.primitives branch outside χ f).coeff := by
  simp only [primitives, assemble_value, PrimitiveKey, Fintype.sum_sum_type, Fintype.sum_prod_type]
  funext z
  simp only [Pi.add_apply, Finset.sum_apply, SpinGlass.SKFastEvaluator.primitives,
    SpinGlass.SKRing.coeff_add]
  rw [← add_assoc]
  simp only [SpinGlass.SKRing.coeff_sum, Finset.sum_apply]
  simp only [primitiveInstruction]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro S hS
      by_cases hs : 3 ≤ S.card <;>
        simp [hs, insertInstruction_value, cachedCycle_value]
    · apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hac : a < c
      · simp only [hac, true_and, if_true, SpinGlass.SKRing.coeff_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hs : 1 ≤ S.card <;> by_cases hcut : S.card+1 ≤ L <;>
          simp [hs, hcut, insertInstruction_value, cachedPath_value, insertMonomial]
      · simp [hac]
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hs : 2 ≤ S.card <;> by_cases hcut : S.card+1 ≤ L <;>
      simp [hs, hcut, insertInstruction_value, cachedReturn_value, insertMonomial]


/-- Every primitive coefficient is evaluated once and inserted by one scalar
addition; invalid states are charged no arithmetic. -/
theorem primitiveAssembly_operations_le {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (f : Finset V → ℝ) (cache : Root W b → Table W L) :
    (assemble (primitiveInstruction branch outside f cache)).operations ≤
      SpinGlass.SKOperationCount.closureWork (Fintype.card W) b L := by
  have hcycle (S : Finset (Fin L)) : instructionCost
      (primitiveInstruction branch outside f cache (Sum.inl S)) ≤ 2 * (Fintype.card W) ^ 2 + 2 := by
    simp only [primitiveInstruction]
    split_ifs
    · have hi := insertInstruction_cost_le S.card S (fun _ : Fin b => 0) (cachedCycle outside f cache S)
      have hc := cachedCycle_operations_le outside f cache S
      omega
    · simp [instructionCost, noInstruction]
  have hpath (a c : Fin b) (S : Finset (Fin L)) : instructionCost
      (primitiveInstruction branch outside f cache (Sum.inr (Sum.inl (a, c, S)))) ≤ 2 * Fintype.card W + 1 := by
    simp only [primitiveInstruction]
    split_ifs
    · simpa only [cachedPath_operations] using
        insertInstruction_cost_le (S.card + 1) S (pathDegrees a c) (cachedPath branch outside f cache a c S)
    all_goals simp [instructionCost, noInstruction]
  have hreturn (a : Fin b) (S : Finset (Fin L)) : instructionCost
      (primitiveInstruction branch outside f cache (Sum.inr (Sum.inr (a, S)))) ≤ 2 * Fintype.card W + 2 := by
    simp only [primitiveInstruction]
    split_ifs
    · have hi := insertInstruction_cost_le (S.card + 1) S (pathDegrees a a) (cachedReturn branch outside f cache a S)
      have hc := cachedReturn_operations_le branch outside f cache a S
      omega
    all_goals simp [instructionCost, noInstruction]
  simp only [assemble_operations, PrimitiveKey, Fintype.sum_sum_type, Fintype.sum_prod_type]
  calc
    _ ≤ (∑ _S : Finset (Fin L), (2 * (Fintype.card W) ^ 2 + 2)) +
        ((∑ _a : Fin b, ∑ _c : Fin b, ∑ _S : Finset (Fin L), (2 * Fintype.card W + 1)) +
          ∑ _a : Fin b, ∑ _S : Finset (Fin L), (2 * Fintype.card W + 2)) := by
      apply add_le_add (Finset.sum_le_sum (fun S _ => hcycle S))
      apply add_le_add
      · exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun S _ => hpath a c S)))
      · exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun S _ => hreturn a S))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_id, SpinGlass.SKOperationCount.closureWork]
      ring

/-- The complete executed primitive construction obeys the precise table and
closure profile, now linked to actual saved-array computations. -/
theorem primitives_operations_le {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) :
    (primitives branch outside χ f).operations ≤
      SpinGlass.SKOperationCount.tableWork (Fintype.card W) b L +
        SpinGlass.SKOperationCount.closureWork (Fintype.card W) b L :=
  add_le_add (rootCache_operations_le branch outside χ f)
    (primitiveAssembly_operations_le branch outside f _)

end SpinGlass.SKCountedExecution
