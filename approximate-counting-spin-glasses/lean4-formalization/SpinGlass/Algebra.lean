import SpinGlass.Degree
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
# Finite degree and square-zero color monomials

This file packages the proved degree operation as a six-element additive
commutative monoid. It also verifies the multiplication and nilpotence of
color-support monomials. It does not construct or certify the paper's entire
multivariate coefficient algebra or its dynamic-programming algorithm.
-/

namespace SpinGlass.CappedDegree

instance : AddCommMonoid CappedDegree where
  add := add
  zero := 0
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- The wrapper's states are in bijection with the six canonical exponents. -/
def equivFin : CappedDegree ≃ Fin 6 where
  toFun := CappedDegree.toFin
  invFun := fun i => ⟨i⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro i; rfl

instance : Fintype CappedDegree := Fintype.ofEquiv (Fin 6) equivFin.symm

@[simp] theorem card_eq_six : Fintype.card CappedDegree = 6 := by
  calc
    Fintype.card CappedDegree = Fintype.card (Fin 6) := Fintype.card_congr equivFin
    _ = 6 := Fintype.card_fin 6

end SpinGlass.CappedDegree


namespace SpinGlass.ColorSupport

variable {Color Vertex : Type*} [DecidableEq Color]

/-- A color monomial is either annihilated (`none`) or indexed by a color subset. -/
abbrev Monomial (Color : Type*) := Option (Finset Color)

/-- Square-zero color multiplication, before attaching coefficients. -/
def mul : Monomial Color → Monomial Color → Monomial Color
  | some S, some T => if Disjoint S T then some (S ∪ T) else none
  | _, _ => none

@[simp] theorem none_mul (a : Monomial Color) : mul none a = none := by
  cases a <;> rfl

@[simp] theorem mul_none (a : Monomial Color) : mul a none = none := by
  cases a <;> rfl

@[simp] theorem mul_of_disjoint (S T : Finset Color) (h : Disjoint S T) :
    mul (some S) (some T) = some (S ∪ T) := by simp [mul, h]

@[simp] theorem mul_of_not_disjoint (S T : Finset Color) (h : ¬ Disjoint S T) :
    mul (some S) (some T) = none := by simp [mul, h]

theorem mul_comm (a b : Monomial Color) : mul a b = mul b a := by
  cases a <;> cases b <;> simp [mul, disjoint_comm, Finset.union_comm]

theorem mul_assoc (a b c : Monomial Color) : mul (mul a b) c = mul a (mul b c) := by
  cases a with
  | none => simp [mul]
  | some S =>
    cases b with
    | none => simp [mul]
    | some T =>
      cases c with
      | none => simp [mul]
      | some U =>
        by_cases hST : Disjoint S T <;>
          by_cases hSU : Disjoint S U <;>
          by_cases hTU : Disjoint T U <;>
          simp [mul, hST, hSU, hTU, Finset.disjoint_union_left, Finset.disjoint_union_right,
            Finset.union_assoc]

@[simp] theorem empty_mul (a : Monomial Color) : mul (some ∅) a = a := by
  cases a <;> simp [mul]

@[simp] theorem mul_empty (a : Monomial Color) : mul a (some ∅) = a := by
  rw [mul_comm, empty_mul]

/-- Every individual color generator squares to zero. -/
theorem singleton_square_zero (c : Color) : mul (some {c}) (some {c}) = none := by
  simp [mul]

/-- Product of finitely many color supports. -/
def prod : List (Finset Color) → Monomial Color
  | [] => some ∅
  | S :: supports => mul (some S) (prod supports)

/-- Every nonempty surviving factor consumes at least one distinct color. -/
theorem prod_some_card_bound (supports : List (Finset Color))
    (hne : ∀ S ∈ supports, S.Nonempty) {U : Finset Color}
    (hprod : prod supports = some U) : supports.length ≤ U.card := by
  induction supports generalizing U with
  | nil =>
    simp only [prod, Option.some.injEq] at hprod
    subst U
    simp
  | cons S supports ih =>
    have hS : S.Nonempty := hne S (by simp)
    have htail : ∀ T ∈ supports, T.Nonempty := by
      intro T hT
      exact hne T (by simp [hT])
    cases hp : prod supports with
    | none => simp [prod, hp, mul] at hprod
    | some T =>
      by_cases hd : Disjoint S T
      · have hU : S ∪ T = U := by simpa [prod, hp, mul, hd] using hprod
        subst U
        have hi := ih htail hp
        have hpos : 0 < S.card := Finset.card_pos.mpr hS
        rw [List.length_cons, Finset.card_union_of_disjoint hd]
        omega
      · simp [prod, hp, mul, hd] at hprod

/-- More nonempty factors than colors must be annihilated. -/
theorem prod_eq_none_of_length_gt [Fintype Color]
    (supports : List (Finset Color))
    (hne : ∀ S ∈ supports, S.Nonempty)
    (hlength : Fintype.card Color < supports.length) : prod supports = none := by
  cases hp : prod supports with
  | none => rfl
  | some U =>
    have hconsumed := prod_some_card_bound supports hne hp
    have havailable := Finset.card_le_univ U
    omega

/-- Monomial form of the paper's nilpotence at the `(L + 1)`st power. -/
theorem prod_eq_none_at_L_succ (L : Nat) (supports : List (Finset (Fin L)))
    (hne : ∀ S ∈ supports, S.Nonempty) (hlength : supports.length = L + 1) :
    prod supports = none := by
  apply prod_eq_none_of_length_gt supports hne
  simp [hlength]

/-- Disjoint color supports imply disjoint vertex supports for any coloring. -/
theorem disjoint_images_implies_disjoint [DecidableEq Vertex]
    (χ : Vertex → Color) (S T : Finset Vertex)
    (h : Disjoint (S.image χ) (T.image χ)) : Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro v hvS hvT
  exact Finset.disjoint_left.mp h
    (Finset.mem_image.mpr ⟨v, hvS, rfl⟩)
    (Finset.mem_image.mpr ⟨v, hvT, rfl⟩)

end SpinGlass.ColorSupport
