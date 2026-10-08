import SpinGlass.Algebra
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# The concrete coefficient arrays used by the SK evaluator

A basis coordinate records the edge count, a subset of colors, and the six-state
branch degrees. Multiplication is the actual dense pair-iteration rule: discard
pairs that reuse a color or exceed the edge cutoff, and otherwise accumulate the
product into its uniquely determined output coordinate.
-/

noncomputable section

namespace SpinGlass.SKCoefficient

open scoped BigOperators

/-- The array coordinates in (63), with `b` branch vertices and `L` colors. -/
abbrev Basis (b L : ℕ) := Fin (L + 1) × Finset (Fin L) × (Fin b → CappedDegree)

/-- Its number of coordinates is exactly the paper's stated dimension. -/
theorem card_basis (b L : ℕ) :
    Fintype.card (Basis b L) = (L + 1) * 2 ^ L * 6 ^ b := by
  simp [Basis, Fintype.card_prod, Fintype.card_finset,
    CappedDegree.card_eq_six, Nat.mul_assoc]

/-- All coefficients, including negative signed weights, are retained. -/
abbrev Coefficients (b L : ℕ) := Basis b L → ℝ

/-- Valid multiplication of two basis coordinates. -/
def compatible {b L : ℕ} (x y : Basis b L) : Prop :=
  x.1.val + y.1.val ≤ L ∧ Disjoint x.2.1 y.2.1

instance {b L : ℕ} (x y : Basis b L) : Decidable (compatible x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The single coordinate receiving a surviving pair's coefficient. -/
def combine {b L : ℕ} (x y : Basis b L) (h : compatible x y) : Basis b L :=
  (⟨x.1.val + y.1.val, Nat.lt_succ_of_le h.1⟩, x.2.1 ∪ y.2.1, fun a => x.2.2 a + y.2.2 a)

/-- Basis multiplication, including annihilation of rejected pairs. -/
def basisMul {b L : ℕ} (x y : Basis b L) : Option (Basis b L) :=
  if h : compatible x y then some (combine x y h) else none

/-- One coefficient update in the dense multiplication procedure. -/
def pairContribution {b L : ℕ} (x y z : Basis b L) (a c : ℝ) : ℝ :=
  if basisMul x y = some z then a * c else 0

/-- Dense coefficient multiplication by explicitly summing all ordered pairs. -/
def mul {b L : ℕ} (f g : Coefficients b L) : Coefficients b L :=
  fun z => ∑ x, ∑ y, pairContribution x y z (f x) (g y)

/-- An individual basis monomial carrying a real coefficient. -/
def single {b L : ℕ} (x : Basis b L) (a : ℝ) : Coefficients b L :=
  fun z => if x = z then a else 0

@[simp] theorem compatible_comm {b L : ℕ} (x y : Basis b L) :
    compatible x y ↔ compatible y x := by
  simp [compatible, Nat.add_comm, disjoint_comm]

theorem basisMul_comm {b L : ℕ} (x y : Basis b L) : basisMul x y = basisMul y x := by
  by_cases h : compatible x y
  · have h' := (compatible_comm x y).mp h
    simp only [basisMul, dif_pos h, dif_pos h', Option.some.injEq]
    unfold combine
    apply Prod.ext
    · apply Fin.ext
      exact Nat.add_comm _ _
    · apply Prod.ext
      · exact Finset.union_comm _ _
      · funext a
        exact add_comm _ _
  · have h' : ¬ compatible y x := by simpa using h
    simp [basisMul, h, h']

/-- Associativity includes both sources of annihilation: colors and edge cutoff. -/
theorem basisMul_assoc {b L : ℕ} (x y z : Basis b L) :
    (basisMul x y).bind (fun u => basisMul u z) =
      (basisMul y z).bind (fun u => basisMul x u) := by
  by_cases ht : x.1.val + y.1.val + z.1.val ≤ L
  · have hxy : x.1.val + y.1.val ≤ L := by omega
    have hyz : y.1.val + z.1.val ≤ L := by omega
    have ht' : x.1.val + (y.1.val + z.1.val) ≤ L := by omega
    by_cases dxy : Disjoint x.2.1 y.2.1 <;>
      by_cases dxz : Disjoint x.2.1 z.2.1 <;>
      by_cases dyz : Disjoint y.2.1 z.2.1
    all_goals simp only [basisMul, compatible, hxy, hyz, dxy, dxz, dyz,
      and_self, and_true, and_false, dite_true, dite_false, Option.bind_some,
      Option.bind_none, combine, ht, ht', Finset.disjoint_union_left,
      Finset.disjoint_union_right]
    all_goals try simp [dxy, dxz, dyz, ht, ht']
    constructor
    · exact Nat.add_assoc _ _ _
    · funext a
      exact add_assoc _ _ _
  · have ht' : ¬ x.1.val + (y.1.val + z.1.val) ≤ L := by omega
    by_cases hxy : compatible x y <;> by_cases hyz : compatible y z
    all_goals simp only [basisMul, hxy, hyz, dite_true, dite_false,
      Option.bind_some, Option.bind_none]
    all_goals simp [compatible, combine, ht, ht']

@[simp] theorem basisMul_eq_none_iff {b L : ℕ} (x y : Basis b L) :
    basisMul x y = none ↔ ¬ compatible x y := by
  unfold basisMul
  split <;> simp_all

/-- The edge count of every surviving update is its exact sum. -/
theorem edgeCount_of_basisMul {b L : ℕ} {x y z : Basis b L}
    (h : basisMul x y = some z) : z.1.val = x.1.val + y.1.val := by
  unfold basisMul at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

/-- The color set of every surviving update is its exact disjoint union. -/
theorem colors_of_basisMul {b L : ℕ} {x y z : Basis b L}
    (h : basisMul x y = some z) : z.2.1 = x.2.1 ∪ y.2.1 := by
  unfold basisMul at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

/-- Degree reduction in a surviving update is coordinatewise quotient addition. -/
theorem degree_of_basisMul {b L : ℕ} {x y z : Basis b L}
    (h : basisMul x y = some z) (a : Fin b) : z.2.2 a = x.2.2 a + y.2.2 a := by
  unfold basisMul at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

@[simp] theorem pairContribution_zero_left {b L : ℕ} (x y z : Basis b L) (a : ℝ) :
    pairContribution x y z 0 a = 0 := by simp [pairContribution]

@[simp] theorem pairContribution_zero_right {b L : ℕ} (x y z : Basis b L) (a : ℝ) :
    pairContribution x y z a 0 = 0 := by simp [pairContribution]

/-- Multiplying individual basis monomials performs exactly one accepted update. -/
theorem mul_single_single {b L : ℕ} (x y : Basis b L) (a c : ℝ) :
    mul (single x a) (single y c) =
      fun z => pairContribution x y z a c := by
  funext z
  unfold mul
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp [single]
    · intro y' hy' hne
      have hn : y ≠ y' := Ne.symm hne
      simp [single, hn]
    · simp
  · intro x' hx' hne
    have hn : x ≠ x' := Ne.symm hne
    simp [single, hn]
  · simp

/-- Rejected basis pairs vanish identically. -/
theorem mul_single_single_rejected {b L : ℕ} (x y : Basis b L) (a c : ℝ)
    (h : ¬ compatible x y) : mul (single x a) (single y c) = 0 := by
  rw [mul_single_single]
  funext z
  simp [pairContribution, basisMul, h]

/-- Accepted basis pairs have precisely the claimed product coefficient. -/
theorem mul_single_single_accepted {b L : ℕ} (x y : Basis b L) (a c : ℝ)
    (h : compatible x y) :
    mul (single x a) (single y c) = single (combine x y h) (a * c) := by
  rw [mul_single_single]
  funext z
  simp [pairContribution, basisMul, h, single]

theorem mul_comm {b L : ℕ} (f g : Coefficients b L) : mul f g = mul g f := by
  funext z
  rw [mul, mul, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp [pairContribution, basisMul_comm y x, _root_.mul_comm]

theorem mul_add {b L : ℕ} (f g h : Coefficients b L) :
    mul f (g + h) = mul f g + mul f h := by
  funext z
  simp only [mul, pairContribution, Pi.add_apply, _root_.mul_add]
  simp_rw [ite_add_zero, Finset.sum_add_distrib]

@[simp] theorem mul_zero {b L : ℕ} (f : Coefficients b L) : mul f 0 = 0 := by
  funext z
  simp [mul]

@[simp] theorem zero_mul {b L : ℕ} (f : Coefficients b L) : mul 0 f = 0 := by
  rw [mul_comm, mul_zero]

theorem add_mul {b L : ℕ} (f g h : Coefficients b L) :
    mul (f + g) h = mul f h + mul g h := by
  rw [mul_comm, mul_add, mul_comm h f, mul_comm h g]

theorem mul_sum {b L : ℕ} {I : Type*} (s : Finset I)
    (f : Coefficients b L) (g : I → Coefficients b L) :
    mul f (∑ i ∈ s, g i) = ∑ i ∈ s, mul f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, mul_add, ih]

theorem sum_mul {b L : ℕ} {I : Type*} (s : Finset I)
    (f : I → Coefficients b L) (g : Coefficients b L) :
    mul (∑ i ∈ s, f i) g = ∑ i ∈ s, mul (f i) g := by
  rw [mul_comm, mul_sum]
  simp_rw [mul_comm g]

/-- Every coefficient array is exactly the sum of its weighted basis vectors. -/
theorem sum_single {b L : ℕ} (f : Coefficients b L) :
    (∑ x, single x (f x)) = f := by
  funext z
  simp only [Finset.sum_apply, single]
  simp

/-- Extend a monomial by zero at the rejected coordinate. -/
def optionSingle {b L : ℕ} (x : Option (Basis b L)) (a : ℝ) : Coefficients b L :=
  x.elim 0 (fun z => single z a)

theorem mul_single_single_option {b L : ℕ} (x y : Basis b L) (a c : ℝ) :
    mul (single x a) (single y c) = optionSingle (basisMul x y) (a * c) := by
  rw [mul_single_single]
  funext z
  cases hp : basisMul x y <;> simp [hp, pairContribution, optionSingle, single]

theorem optionSingle_mul_single {b L : ℕ} (x : Option (Basis b L))
    (y : Basis b L) (a c : ℝ) :
    mul (optionSingle x a) (single y c) =
      optionSingle (x.bind (fun z => basisMul z y)) (a * c) := by
  cases x <;> simp [optionSingle, mul_single_single_option]

theorem single_mul_optionSingle {b L : ℕ} (x : Basis b L)
    (y : Option (Basis b L)) (a c : ℝ) :
    mul (single x a) (optionSingle y c) =
      optionSingle (y.bind (fun z => basisMul x z)) (a * c) := by
  cases y <;> simp [optionSingle, mul_single_single_option]

theorem mul_single_assoc {b L : ℕ} (x y z : Basis b L) (a c d : ℝ) :
    mul (mul (single x a) (single y c)) (single z d) =
      mul (single x a) (mul (single y c) (single z d)) := by
  rw [mul_single_single_option, mul_single_single_option,
    optionSingle_mul_single, single_mul_optionSingle, basisMul_assoc, _root_.mul_assoc]

/-- Dense coefficient multiplication is associative, including all discarded pairs. -/
theorem mul_assoc {b L : ℕ} (f g h : Coefficients b L) :
    mul (mul f g) h = mul f (mul g h) := by
  conv_lhs => rw [← sum_single f, ← sum_single g, ← sum_single h]
  conv_rhs => rw [← sum_single f, ← sum_single g, ← sum_single h]
  simp_rw [sum_mul, mul_sum, sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  exact mul_single_assoc x y z (f x) (g y) (h z)

/-- The coordinate of the constant monomial. -/
def oneBasis (b L : ℕ) : Basis b L := (0, ∅, fun _ => 0)

/-- The multiplicative identity coefficient array. -/
def one (b L : ℕ) : Coefficients b L := single (oneBasis b L) 1

@[simp] theorem basisMul_one {b L : ℕ} (x : Basis b L) :
    basisMul x (oneBasis b L) = some x := by
  have hx : x.1.val ≤ L := by omega
  simp [basisMul, compatible, oneBasis, hx, combine]

@[simp] theorem mul_one {b L : ℕ} (f : Coefficients b L) : mul f (one b L) = f := by
  conv_lhs => rw [← sum_single f]
  rw [sum_mul]
  simp only [one, mul_single_single_option, basisMul_one, optionSingle, Option.elim_some,
    _root_.mul_one]
  exact sum_single f

@[simp] theorem one_mul {b L : ℕ} (f : Coefficients b L) : mul (one b L) f = f := by
  rw [mul_comm, mul_one]

/-- Scalar multiplication is pointwise on real coefficient arrays. -/
def scale {b L : ℕ} (a : ℝ) (f : Coefficients b L) : Coefficients b L := fun z => a * f z

@[simp] theorem scale_one {b L : ℕ} (f : Coefficients b L) : scale 1 f = f := by
  funext z
  simp [scale]

theorem scale_scale {b L : ℕ} (a c : ℝ) (f : Coefficients b L) :
    scale a (scale c f) = scale (a * c) f := by
  funext z
  simp [scale, _root_.mul_assoc]

theorem scale_mul {b L : ℕ} (a : ℝ) (f g : Coefficients b L) :
    mul (scale a f) g = scale a (mul f g) := by
  funext z
  simp only [mul, pairContribution, scale, Finset.mul_sum, _root_.mul_assoc]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  split <;> simp_all

/-- Recursive powers use the proved dense multiplication, not pointwise products. -/
def pow {b L : ℕ} (f : Coefficients b L) : ℕ → Coefficients b L
  | 0 => one b L
  | n + 1 => mul (pow f n) f

/-- An array has no monomial below a specified number of consumed colors. -/
def VanishesBelow {b L : ℕ} (n : ℕ) (f : Coefficients b L) : Prop :=
  ∀ z, z.2.1.card < n → f z = 0

/-- Nonzero products consume the sum of the two disjoint color counts. -/
theorem colorCard_of_basisMul {b L : ℕ} {x y z : Basis b L}
    (h : basisMul x y = some z) : z.2.1.card = x.2.1.card + y.2.1.card := by
  have hc : compatible x y := by
    by_contra hn
    simp [basisMul, hn] at h
  rw [colors_of_basisMul h, Finset.card_union_of_disjoint hc.2]

theorem vanishesBelow_mul {b L m n : ℕ} {f g : Coefficients b L}
    (hf : VanishesBelow m f) (hg : VanishesBelow n g) :
    VanishesBelow (m + n) (mul f g) := by
  intro z hz
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  unfold pairContribution
  split
  next h =>
    have hc := colorCard_of_basisMul h
    by_cases hxm : x.2.1.card < m
    · rw [hf x hxm, MulZeroClass.zero_mul]
    · have hyn : y.2.1.card < n := by omega
      rw [hg y hyn, MulZeroClass.mul_zero]
  next h => rfl

theorem vanishesBelow_pow {b L : ℕ} (f : Coefficients b L)
    (hf : VanishesBelow 1 f) (n : ℕ) : VanishesBelow n (pow f n) := by
  induction n with
  | zero => intro z hz; omega
  | succ n ih => exact vanishesBelow_mul ih hf

/-- The color ideal is nilpotent with exactly the paper's uniform exponent. -/
theorem pow_colors_succ_eq_zero {b L : ℕ} (f : Coefficients b L)
    (hf : VanishesBelow 1 f) : pow f (L + 1) = 0 := by
  funext z
  have hcard : z.2.1.card ≤ L := by simpa using Finset.card_le_univ z.2.1
  exact vanishesBelow_pow f hf (L + 1) z (by omega)

/-- Exactly the squared number of basis coordinates are visited by a dense product. -/
theorem card_multiplication_pairs (b L : ℕ) :
    Fintype.card (Basis b L × Basis b L) = (L + 1) ^ 2 * 4 ^ L * 36 ^ b := by
  rw [Fintype.card_prod, card_basis]
  have h4 : (4 : ℕ) ^ L = (2 ^ L) ^ 2 := by
    rw [← Nat.pow_mul, Nat.mul_comm L 2, Nat.pow_mul]
  have h36 : (36 : ℕ) ^ b = (6 ^ b) ^ 2 := by
    rw [← Nat.pow_mul, Nat.mul_comm b 2, Nat.pow_mul]
  rw [h4, h36]
  ring

/-- Multivariate coefficient extraction accepts exactly the required branch degrees. -/
theorem all_branch_states_four_iff {b : ℕ} (d : Fin b → ℕ) :
    (∀ a, (CappedDegree.ofNat (d a)).val = 4) ↔
      ∀ a, 4 ≤ d a ∧ d a % 2 = 0 := by
  simp only [CappedDegree.val_ofNat, rho_eq_four_iff]

end SpinGlass.SKCoefficient
