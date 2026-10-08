import SpinGlass.LocalCube
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Explicit real-arithmetic evaluation and its operation counter

Every addition or multiplication increments the counter. Finite sums and
products are evaluated by actual recursive list traversals, rather than being
assigned an asymptotic cost. Literal real inputs are available at zero cost.
-/

noncomputable section
namespace SpinGlass.ArithmeticEvaluation
open Finset

structure Computation where
  value : ℝ
  operations : ℕ

def literal (x : ℝ) : Computation := ⟨x, 0⟩
def add (x y : Computation) : Computation := ⟨x.value+y.value, x.operations+y.operations+1⟩
def mul (x y : Computation) : Computation := ⟨x.value*y.value, x.operations+y.operations+1⟩

def sumList : List Computation → Computation
  | [] => literal 0
  | x :: xs => add x (sumList xs)

def productList : List Computation → Computation
  | [] => literal 1
  | x :: xs => mul x (productList xs)

@[simp] theorem sumList_value (xs : List Computation) :
    (sumList xs).value = (xs.map Computation.value).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumList, add, ih]

@[simp] theorem productList_value (xs : List Computation) :
    (productList xs).value = (xs.map Computation.value).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [productList, mul, ih]

@[simp] theorem sumList_operations (xs : List Computation) :
    (sumList xs).operations = (xs.map Computation.operations).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumList, add, ih]; omega

@[simp] theorem productList_operations (xs : List Computation) :
    (productList xs).operations = (xs.map Computation.operations).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [productList, mul, ih]; omega

def sumFinset {ι : Type*} (s : Finset ι) (f : ι → Computation) : Computation :=
  sumList (s.toList.map f)
def productFinset {ι : Type*} (s : Finset ι) (f : ι → Computation) : Computation :=
  productList (s.toList.map f)

@[simp] theorem sumFinset_value {ι : Type*} (s : Finset ι) (f : ι → Computation) :
    (sumFinset s f).value = ∑ i ∈ s, (f i).value := by
  simp [sumFinset, List.map_map, Function.comp_def]

@[simp] theorem productFinset_value {ι : Type*} (s : Finset ι) (f : ι → Computation) :
    (productFinset s f).value = ∏ i ∈ s, (f i).value := by
  simp [productFinset, List.map_map, Function.comp_def]

@[simp] theorem sumFinset_operations {ι : Type*} (s : Finset ι) (f : ι → Computation) :
    (sumFinset s f).operations = (∑ i ∈ s, (f i).operations) + s.card := by
  simp [sumFinset, List.map_map, Function.comp_def]

@[simp] theorem productFinset_operations {ι : Type*} (s : Finset ι) (f : ι → Computation) :
    (productFinset s f).operations = (∑ i ∈ s, (f i).operations) + s.card := by
  simp [productFinset, List.map_map, Function.comp_def]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The normalization is computed by `|S|` multiplications by one half. -/
def cubeNormalizer (S : Finset V) : Computation :=
  productFinset (Finset.range S.card) (fun _ => literal (1/2))

/-- A local edge character is computed by multiplying the individual spins. -/
def character (S : Finset V) (σ : S → Bool) (e : Finset V) : Computation :=
  productFinset (SpinGlass.LocalCube.localIncidence S e)
    (fun v => literal (SpinGlass.Expansion.spinSign (σ v)))

/-- One factor in the local high-temperature expansion. -/
def edgeFactor (weight : Finset V → ℝ) (S : Finset V) (σ : S → Bool) (e : Finset V) : Computation :=
  add (literal 1) (mul (literal (weight e)) (character S σ e))

/-- One complete product, for one local spin configuration. -/
def spinTerm (edges : Finset (Finset V)) (weight : Finset V → ℝ)
    (S : Finset V) (σ : S → Bool) : Computation :=
  productFinset (edges.filter (fun e => e ⊆ S)) (edgeFactor weight S σ)

/-- The actual local-cube evaluator enumerates only the `2^|S|` local assignments. -/
def localEvaluator (edges : Finset (Finset V)) (weight : Finset V → ℝ)
    (S : Finset V) : Computation :=
  mul (cubeNormalizer S) (sumFinset Finset.univ (spinTerm edges weight S))

@[simp] theorem cubeNormalizer_value (S : Finset V) :
    (cubeNormalizer S).value = ((2 : ℝ)^S.card)⁻¹ := by
  simp [cubeNormalizer, literal, one_div, inv_pow]

@[simp] theorem cubeNormalizer_operations (S : Finset V) :
    (cubeNormalizer S).operations = S.card := by simp [cubeNormalizer, literal]

@[simp] theorem character_value (S : Finset V) (σ : S → Bool) (e : Finset V) :
    (character S σ e).value = SpinGlass.Expansion.edgeCharacter (SpinGlass.LocalCube.localIncidence S) σ e := by
  simp [character, literal, SpinGlass.Expansion.edgeCharacter]

@[simp] theorem character_operations (S : Finset V) (σ : S → Bool) (e : Finset V) :
    (character S σ e).operations = (SpinGlass.LocalCube.localIncidence S e).card := by
  simp [character, literal]

/-- The computed value agrees with the previously proved exact local spin sum. -/
theorem localEvaluator_value (edges : Finset (Finset V)) (weight : Finset V → ℝ)
    (S : Finset V) :
    (localEvaluator edges weight S).value = SpinGlass.LocalCube.localGspin edges weight S := by
  simp [localEvaluator, spinTerm, edgeFactor, add, mul, literal,
    SpinGlass.LocalCube.localGspin, SpinGlass.Expansion.spinMean]

/-- The exact arithmetic-operation count of the local spin evaluator. -/
theorem localEvaluator_operations (edges : Finset (Finset V)) (weight : Finset V → ℝ)
    (S : Finset V) :
    (localEvaluator edges weight S).operations = S.card +
      2^S.card * ((∑ e ∈ edges.filter (fun e => e ⊆ S),
        (SpinGlass.LocalCube.localIncidence S e).card) +
        3 * (edges.filter (fun e => e ⊆ S)).card + 1) + 1 := by
  simp only [localEvaluator, mul, cubeNormalizer_operations, sumFinset_operations,
    spinTerm, productFinset_operations, edgeFactor, add, literal, character_operations,
    Nat.zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_coe, nsmul_eq_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  ring

end SpinGlass.ArithmeticEvaluation
