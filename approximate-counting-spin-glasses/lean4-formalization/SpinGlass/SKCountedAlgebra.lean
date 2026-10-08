import SpinGlass.SKCountedExecutionCore
import SpinGlass.SKOperationCount
import SpinGlass.InputPreparation

/-! # Counted point-update coefficient algebra execution

Counters are propagated from actual scalar arithmetic instructions and sequential
loops. Saved coefficient arrays are read as literal registers; a product is
executed once and materialized before scaling or addition reads it.
-/
noncomputable section
namespace SpinGlass.SKCountedAlgebra
open scoped BigOperators
open SKCountedExecution SKCoefficient
open SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation

/-- A surviving basis pair executes one multiply and one accumulating addition. -/
def step {b L : ℕ} (f g : Coefficients b L) (p : Basis b L × Basis b L)
    (state : Counted (Coefficients b L)) : Counted (Coefficients b L) :=
  match basisMul p.1 p.2 with
  | none => state
  | some z =>
      let result := ArithmeticEvaluation.add (literal (state.value z))
        (ArithmeticEvaluation.mul (literal (f p.1)) (literal (g p.2)))
      ⟨Function.update state.value z result.value, state.operations + result.operations⟩

theorem step_value {b L : ℕ} (f g : Coefficients b L) (p : Basis b L × Basis b L)
    (state : Counted (Coefficients b L)) :
    (step f g p state).value = SKDenseExecution.pushStep f g p state.value := by
  unfold step SKDenseExecution.pushStep
  cases basisMul p.1 p.2 <;> rfl

theorem step_operations {b L : ℕ} (f g : Coefficients b L) (p : Basis b L × Basis b L)
    (state : Counted (Coefficients b L)) :
    (step f g p state).operations = state.operations + SKDenseExecution.stepArithmetic p := by
  by_cases h : compatible p.1 p.2
  · simp [step, basisMul, h, ArithmeticEvaluation.add, ArithmeticEvaluation.mul, literal,
      SKDenseExecution.stepArithmetic]
  · simp [step, basisMul, h, SKDenseExecution.stepArithmetic]

/-- Literal sequential basis-pair execution with stored coefficient registers. -/
def loop {b L : ℕ} (f g : Coefficients b L) :
    List (Basis b L × Basis b L) → Counted (Coefficients b L) → Counted (Coefficients b L)
  | [], state => state
  | p :: ps, state => loop f g ps (step f g p state)

theorem loop_value {b L : ℕ} (f g : Coefficients b L)
    (ps : List (Basis b L × Basis b L)) (state : Counted (Coefficients b L)) :
    (loop f g ps state).value = SKDenseExecution.pushLoop f g ps state.value := by
  induction ps generalizing state with
  | nil => rfl
  | cons p ps ih => rw [loop, ih, step_value]; rfl

theorem loop_operations {b L : ℕ} (f g : Coefficients b L)
    (ps : List (Basis b L × Basis b L)) (state : Counted (Coefficients b L)) :
    (loop f g ps state).operations = state.operations + SKDenseExecution.loopArithmetic ps := by
  induction ps generalizing state with
  | nil => simp [loop, SKDenseExecution.loopArithmetic]
  | cons p ps ih => rw [loop, ih, step_operations, SKDenseExecution.loopArithmetic, Nat.add_assoc]

def denseMul {b L : ℕ} (f g : Coefficients b L) : Counted (Coefficients b L) :=
  loop f g Finset.univ.toList ⟨0,0⟩

@[simp] theorem denseMul_value {b L : ℕ} (f g : Coefficients b L) :
    (denseMul f g).value = SKCoefficient.mul f g := by
  rw [denseMul, loop_value]
  exact SKDenseExecution.denseMul_correct f g

theorem denseMul_operations_le {b L : ℕ} (f g : Coefficients b L) :
    (denseMul f g).operations ≤ 2 * SKOperationCount.registers b L ^ 2 := by
  simp only [denseMul, loop_operations, zero_add]
  rw [SKOperationCount.registers_sq]
  simpa only [Nat.mul_assoc] using SKDenseExecution.denseMul_arithmetic_bound b L

/-- Each scalar array operation materializes all output coordinates once. -/
def scaleArray {b L : ℕ} (a : ℝ) (f : Coefficients b L) : Counted (Coefficients b L) :=
  tabulate (fun z => ofComputation (ArithmeticEvaluation.mul (literal a) (literal (f z))))

def addArray {b L : ℕ} (f g : Coefficients b L) : Counted (Coefficients b L) :=
  tabulate (fun z => ofComputation (ArithmeticEvaluation.add (literal (f z)) (literal (g z))))

@[simp] theorem scaleArray_value {b L : ℕ} (a : ℝ) (f : Coefficients b L) :
    (scaleArray a f).value = scale a f := by
  funext z
  simp [scaleArray, ofComputation, ArithmeticEvaluation.mul, literal, scale]

@[simp] theorem addArray_value {b L : ℕ} (f g : Coefficients b L) :
    (addArray f g).value = f + g := by
  funext z
  simp [addArray, ofComputation, ArithmeticEvaluation.add, literal]

@[simp] theorem scaleArray_operations {b L : ℕ} (a : ℝ) (f : Coefficients b L) :
    (scaleArray a f).operations = SKOperationCount.registers b L := by
  simp [scaleArray, ofComputation, ArithmeticEvaluation.mul, literal,
    SKCoefficient.card_basis, SKOperationCount.registers, Nat.mul_assoc]

@[simp] theorem addArray_operations {b L : ℕ} (f g : Coefficients b L) :
    (addArray f g).operations = SKOperationCount.registers b L := by
  simp [addArray, ofComputation, ArithmeticEvaluation.add, literal,
    SKCoefficient.card_basis, SKOperationCount.registers, Nat.mul_assoc]

/-- Saved-register finite-exponential loop, including reciprocal, scale, and accumulation. -/
def expExecution {b L : ℕ} (f : Coefficients b L) :
    ℕ → Counted (Coefficients b L × Coefficients b L)
  | 0 => ⟨(one b L, one b L), 0⟩
  | n + 1 =>
      let old := expExecution f n
      let product := denseMul old.value.1 f
      let inverse := divide (literal 1) (literal (n + 1 : ℕ))
      let next := scaleArray inverse.value product.value
      let accumulator := addArray old.value.2 next.value
      ⟨(next.value, accumulator.value), old.operations + product.operations + inverse.operations +
        next.operations + accumulator.operations⟩

@[simp] theorem expExecution_value {b L : ℕ} (f : Coefficients b L) (n : ℕ) :
    (expExecution f n).value = SKExponential.expLoop f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expExecution, SKExponential.expLoop, scaleArray_value, addArray_value,
      denseMul_value, ih, divide, literal, one_div]

/-- Uniform cost of any array-multiplication loop iteration. -/
def iterationWork (b L : ℕ) : ℕ :=
  2 * SKOperationCount.registers b L ^ 2 + 2 * SKOperationCount.registers b L + 1

theorem expExecution_operations_le {b L : ℕ} (f : Coefficients b L) (n : ℕ) :
    (expExecution f n).operations ≤ n * iterationWork b L := by
  induction n with
  | zero => simp [expExecution]
  | succ n ih =>
    have hp := denseMul_operations_le (expExecution f n).value.1 f
    simp only [expExecution, scaleArray_operations, addArray_operations, divide, literal] at *
    unfold iterationWork at *
    nlinarith

/-- Direct factors are constructed in stored arrays and multiplied one at a time. -/
def directExecution {b L : ℕ} : List (Coefficients b L) →
    Coefficients b L → Counted (Coefficients b L)
  | [], acc => ⟨acc,0⟩
  | e :: es, acc =>
      let factor := addArray (one b L) e
      let product := denseMul acc factor.value
      let rest := directExecution es product.value
      ⟨rest.value, factor.operations + product.operations + rest.operations⟩

@[simp] theorem directExecution_value {b L : ℕ} (es : List (Coefficients b L))
    (acc : Coefficients b L) :
    (directExecution es acc).value = SKExponential.directLoop es acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih => simp only [directExecution, ih, addArray_value, denseMul_value,
      SKExponential.directLoop]

theorem directExecution_operations_le {b L : ℕ} (es : List (Coefficients b L))
    (acc : Coefficients b L) :
    (directExecution es acc).operations ≤ es.length * iterationWork b L := by
  induction es generalizing acc with
  | nil => simp [directExecution]
  | cons e es ih =>
    have hp := denseMul_operations_le acc (addArray (one b L) e).value
    have hi := ih (denseMul acc (addArray (one b L) e).value).value
    simp only [directExecution, addArray_operations, List.length_cons]
    unfold iterationWork at *
    nlinarith

/-- Counted complete algebra execution after primitive and direct-edge caches are available. -/
def evaluator {b L : ℕ} (f : Coefficients b L) (es : List (Coefficients b L)) :
    Counted (Coefficients b L) :=
  let exponential := expExecution f L
  let direct := directExecution es exponential.value.2
  ⟨direct.value, exponential.operations + direct.operations⟩

@[simp] theorem evaluator_value {b L : ℕ} (f : Coefficients b L) (es : List (Coefficients b L)) :
    (evaluator f es).value = SKExponential.algebraEvaluator f es := by
  simp only [evaluator, directExecution_value, expExecution_value, SKExponential.algebraEvaluator]

theorem evaluator_operations_le {b L : ℕ} (f : Coefficients b L) (es : List (Coefficients b L)) :
    (evaluator f es).operations ≤ (L + es.length) * iterationWork b L := by
  have he := expExecution_operations_le f L
  have hd := directExecution_operations_le es (expExecution f L).value.2
  change (expExecution f L).operations + _ ≤ _
  nlinarith

/-- Number of executed compatibility tests in the literal dense pair loop.
The edge-cutoff comparison is followed by a full scan of the `L` color bits;
using a full scan (including after a collision) gives a fixed schedule. -/
def pairTests {b L : ℕ} (_p : Basis b L × Basis b L) : ℕ := 1 + L

def loopTests {b L : ℕ} : List (Basis b L × Basis b L) → ℕ
  | [] => 0
  | p :: ps => pairTests p + loopTests ps

theorem loopTests_eq {b L : ℕ} (ps : List (Basis b L × Basis b L)) :
    loopTests ps = ps.length * (1+L) := by
  induction ps with
  | nil => simp [loopTests]
  | cons p ps ih => simp [loopTests, pairTests, ih, Nat.add_mul]; omega

/-- Exact number of cutoff/color comparisons in one dense multiplication. -/
def denseTests (b L : ℕ) : ℕ :=
  loopTests (Finset.univ.toList : List (Basis b L × Basis b L))

theorem denseTests_eq (b L : ℕ) :
    denseTests b L = SKOperationCount.registers b L ^ 2 * (1+L) := by
  rw [denseTests, loopTests_eq]
  simp only [Finset.length_toList, Finset.card_univ]
  rw [Fintype.card_prod (α := Basis b L) (β := Basis b L), SKCoefficient.card_basis]
  unfold SKOperationCount.registers
  ring

/-- Metadata/register visits in the same pair loop, with a full color scan,
branch-coordinate addition, three reads, one write, and iterator advances.
This conservative schedule charges every pair for the accepted branch too. -/
def loopControl {b L : ℕ} : List (Basis b L × Basis b L) → ℕ
  | [] => 1
  | _ :: ps => 10 * (b + L + 1)^2 + loopControl ps

theorem loopControl_eq {b L : ℕ} (ps : List (Basis b L × Basis b L)) :
    loopControl ps = 1 + ps.length * (10 * (b + L + 1)^2) := by
  induction ps with
  | nil => simp [loopControl]
  | cons p ps ih => simp [loopControl, ih, Nat.add_mul]; omega

def denseControl (b L : ℕ) : ℕ :=
  SKOperationCount.registers b L +
    loopControl (Finset.univ.toList : List (Basis b L × Basis b L))

theorem denseControl_eq (b L : ℕ) :
    denseControl b L = SKOperationCount.registers b L + 1 +
      SKOperationCount.registers b L ^ 2 * (10 * (b+L+1)^2) := by
  rw [denseControl, loopControl_eq]
  simp only [Finset.length_toList, Finset.card_univ]
  rw [Fintype.card_prod (α := Basis b L) (β := Basis b L), SKCoefficient.card_basis]
  unfold SKOperationCount.registers
  ring

/-- Each scalar array pass charges an iterator test/advance and register
reads/write at each coordinate, including its terminating test. -/
def arrayControl (b L : ℕ) : ℕ := 1 + 4 * SKOperationCount.registers b L

def iterationControl (b L : ℕ) : ℕ :=
  denseControl b L + 2 * arrayControl b L + 4

/-- Control follows exactly the same recursion as `expExecution`. -/
def expControl (b L : ℕ) : ℕ → ℕ
  | 0 => 1 + 2 * SKOperationCount.registers b L
  | n+1 => expControl b L n + iterationControl b L

@[simp] theorem expControl_eq (b L n : ℕ) :
    expControl b L n = 1 + 2 * SKOperationCount.registers b L +
      n * iterationControl b L := by
  induction n with
  | zero => simp [expControl]
  | succ n ih => simp [expControl, ih, Nat.add_mul]; omega

/-- The direct loop has one array pass and one dense pair pass per edge. -/
def directControl {b L : ℕ} : List (Coefficients b L) → ℕ
  | [] => 1
  | _ :: es => denseControl b L + arrayControl b L + 4 + directControl es

theorem directControl_le {b L : ℕ} (es : List (Coefficients b L)) :
    directControl es ≤ 1 + es.length * iterationControl b L := by
  induction es with
  | nil => simp [directControl]
  | cons e es ih =>
    simp only [directControl, List.length_cons]
    unfold iterationControl at *
    nlinarith

/-- The sum of arithmetic instructions and the explicit structural schedule. -/
def totalEvaluatorWork {b L : ℕ} (f : Coefficients b L) (es : List (Coefficients b L)) : ℕ :=
  (evaluator f es).operations + expControl b L L + directControl es

theorem totalEvaluatorWork_le {b L : ℕ} (f : Coefficients b L) (es : List (Coefficients b L)) :
    totalEvaluatorWork f es ≤ 2 + 2 * SKOperationCount.registers b L +
      (L + es.length) * (iterationWork b L + iterationControl b L) := by
  have ha := evaluator_operations_le f es
  have hd := directControl_le es
  unfold totalEvaluatorWork
  rw [expControl_eq]
  nlinarith

/-- A fixed polynomial also covers the complete dense-loop metadata schedule. -/
theorem totalEvaluatorWork_bound {b L N : ℕ} (hb : b ≤ N)
    (f : Coefficients b L) (es : List (Coefficients b L)) (hes : es.length ≤ b^2) :
    totalEvaluatorWork f es ≤ 128 * (N+L+1)^6 * 4^L * 36^b := by
  let M := N+L+1
  let T := 4^L * 36^b
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hL : L ≤ M := by dsimp [M]; omega
  have hbM : b ≤ M := by dsimp [M]; omega
  have hBL : b+L+1 ≤ M := by dsimp [M]; omega
  have hL1 : L+1 ≤ M := by dsimp [M]; omega
  have hT : 1 ≤ T := Nat.succ_le_of_lt (by dsimp [T]; positivity)
  have hM2 : M ≤ M^2 := by nlinarith
  have h24 : M^2 ≤ M^4 := Nat.pow_le_pow_right hM (by omega)
  have h46 : M^4 ≤ M^6 := Nat.pow_le_pow_right hM (by omega)
  have hreg2 : SKOperationCount.registers b L ^ 2 ≤ M^2*T := by
    rw [SKOperationCount.registers_sq]
    dsimp [T]
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (36^b) (Nat.mul_le_mul_right (4^L) (Nat.pow_le_pow_left hL1 2))
  have hregpos : 1 ≤ SKOperationCount.registers b L :=
    Nat.succ_le_of_lt (by unfold SKOperationCount.registers; positivity)
  have hreg : SKOperationCount.registers b L ≤ M^2*T := by
    have : SKOperationCount.registers b L ≤ SKOperationCount.registers b L ^ 2 := by nlinarith
    exact this.trans hreg2
  have hblock : iterationWork b L + iterationControl b L ≤ 32*M^4*T := by
    unfold iterationWork iterationControl arrayControl
    rw [denseControl_eq]
    calc
      _ ≤ 2*(M^2*T) + 2*(M^2*T)+1 +
          (M^2*T+1+M^2*T*(10*M^2)+2*(1+4*(M^2*T))+4) := by gcongr
      _ ≤ 32*M^4*T := by
        nlinarith [Nat.mul_le_mul_right T h24, Nat.mul_le_mul hT hM]
  have hlen : L+es.length ≤ 2*M^2 := by
    have : b^2 ≤ M^2 := Nat.pow_le_pow_left hbM 2
    omega
  calc
    totalEvaluatorWork f es ≤ 2+2*SKOperationCount.registers b L +
        (L+es.length)*(iterationWork b L+iterationControl b L) := totalEvaluatorWork_le f es
    _ ≤ 2+2*(M^2*T)+(2*M^2)*(32*M^4*T) := by gcongr
    _ ≤ 128*M^6*T := by
      nlinarith [Nat.mul_le_mul_right T (h24.trans h46), Nat.mul_le_mul hT hM]
    _ = _ := by dsimp [M,T]; ring

end SpinGlass.SKCountedAlgebra
