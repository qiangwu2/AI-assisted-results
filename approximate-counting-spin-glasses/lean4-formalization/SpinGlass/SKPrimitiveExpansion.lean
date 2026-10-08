import SpinGlass.SKRing
import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Primitive selection and the exact factorial cancellation

These theorems connect the executable finite exponential loop to an unordered
finite selection of concrete primitive monomials. They prove the cancellation of
ordered primitive multiplicities by the factorial denominators, including all
color and edge-budget annihilations in the actual coefficient algebra.
-/

noncomputable section
namespace SpinGlass.SKPrimitiveExpansion

open scoped BigOperators
open SKRing

/-- The concrete finite loop is the nilpotent algebra exponential. -/
theorem loop_eq_exp {b L : ℕ} (f : Element b L)
    (hf : SKCoefficient.VanishesBelow 1 f.coeff) :
    (SKExponential.expLoop f.coeff L).2 = (IsNilpotent.exp f).coeff := by
  rw [IsNilpotent.exp_eq_sum (color_ideal_pow_zero f hf), coeff_sum]
  simp_rw [factorial_term_coeff]
  exact (SKExponential.expLoop_invariant f.coeff L).2

/-- A single square-zero primitive contributes precisely its optional factor. -/
theorem exp_of_sq_zero {b L : ℕ} (f : Element b L) (hf : f ^ 2 = 0) :
    IsNilpotent.exp f = 1 + f := by
  rw [IsNilpotent.exp_eq_sum hf]
  simp [Finset.sum_range_succ]

/-- A sum of color-consuming arrays is color-consuming. -/
theorem sum_vanishesBelow {b L : ℕ} {I : Type*} (s : Finset I)
    (f : I → Element b L) (hf : ∀ i ∈ s, SKCoefficient.VanishesBelow 1 (f i).coeff) :
    SKCoefficient.VanishesBelow 1 (∑ i ∈ s, f i).coeff := by
  classical
  intro z hz
  rw [coeff_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i hi => hf i hi z hz

/-- A primitive basis monomial consumes a color whenever its color set is nonempty. -/
theorem monomial_vanishesBelow {b L : ℕ} (x : SKCoefficient.Basis b L) (a : ℝ)
    (hx : x.2.1.Nonempty) :
    SKCoefficient.VanishesBelow 1 (monomial x a).coeff := by
  intro z hz
  change SKCoefficient.single x a z = 0
  apply if_neg
  intro h
  subst z
  exact (Nat.not_lt_of_ge (Finset.card_pos.mpr hx)) hz

/-- The exact finite exponential is a product of optional primitive factors. -/
theorem exp_sum_sq_zero {b L : ℕ} {I : Type*} (s : Finset I)
    (f : I → Element b L)
    (hf : ∀ i ∈ s, SKCoefficient.VanishesBelow 1 (f i).coeff)
    (hfsq : ∀ i ∈ s, (f i) ^ 2 = 0) :
    IsNilpotent.exp (∑ i ∈ s, f i) = ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have htail : ∀ i ∈ s, SKCoefficient.VanishesBelow 1 (f i).coeff :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have htailsq : ∀ i ∈ s, (f i) ^ 2 = 0 :=
      fun i hi => hfsq i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _)
      ⟨2, hfsq a (Finset.mem_insert_self _ _)⟩
      ⟨L + 1, color_ideal_pow_zero _ (sum_vanishesBelow s f htail)⟩]
    rw [exp_of_sq_zero _ (hfsq a (Finset.mem_insert_self _ _)), ih htail htailsq]

/-- Factorials remove the ordering of primitive selections exactly once. -/
theorem loop_eq_powerset {b L : ℕ} {I : Type*} (s : Finset I)
    (f : I → Element b L)
    (hf : ∀ i ∈ s, SKCoefficient.VanishesBelow 1 (f i).coeff)
    (hfsq : ∀ i ∈ s, (f i) ^ 2 = 0) :
    (SKExponential.expLoop (∑ i ∈ s, f i).coeff L).2 =
      (∑ t ∈ s.powerset, ∏ i ∈ t, f i).coeff := by
  rw [loop_eq_exp _ (sum_vanishesBelow s f hf), exp_sum_sq_zero s f hf hfsq,
    Finset.prod_one_add]

/-- The basis-monomial instance needs only the primitive's nonempty color set. -/
theorem monomial_loop_eq_powerset {b L : ℕ} {I : Type*} (s : Finset I)
    (x : I → SKCoefficient.Basis b L) (a : I → ℝ)
    (hx : ∀ i ∈ s, (x i).2.1.Nonempty) :
    (SKExponential.expLoop (∑ i ∈ s, monomial (x i) (a i)).coeff L).2 =
      (∑ t ∈ s.powerset, ∏ i ∈ t, monomial (x i) (a i)).coeff := by
  apply loop_eq_powerset
  · exact fun i hi => monomial_vanishesBelow _ _ (hx i hi)
  · exact fun i hi => monomial_sq_zero _ _ (hx i hi)

/-- The direct-edge product uses exactly the same concrete multiplication. -/
theorem directProduct_eq {b L : ℕ} (fs : List (Element b L)) :
    SKExponential.directProduct (fs.map Element.coeff) =
      (fs.map (fun f => 1 + f)).prod.coeff := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, List.prod_cons, coeff_mul, coeff_add, coeff_one,
      SKExponential.directProduct, ih]

/-- Complete algebraic loop: independently selected primitives and direct edges. -/
theorem evaluator_eq_selections {b L : ℕ} {I J : Type*} (s : Finset I) (d : Finset J)
    (f : I → Element b L) (g : J → Element b L)
    (hf : ∀ i ∈ s, SKCoefficient.VanishesBelow 1 (f i).coeff)
    (hfsq : ∀ i ∈ s, (f i) ^ 2 = 0) :
    SKExponential.algebraEvaluator (∑ i ∈ s, f i).coeff
      (d.toList.map (fun j => (g j).coeff)) =
      ((∑ t ∈ s.powerset, ∏ i ∈ t, f i) *
        (∑ u ∈ d.powerset, ∏ j ∈ u, g j)).coeff := by
  classical
  rw [SKExponential.algebraEvaluator, SKExponential.directLoop_correct,
    loop_eq_powerset s f hf hfsq]
  have hd : SKExponential.directProduct (d.toList.map (fun j => (g j).coeff)) =
      (∏ j ∈ d, (1 + g j)).coeff := by
    simpa [List.map_map, Function.comp_def, Finset.prod_toList] using directProduct_eq (d.toList.map g)
  rw [hd, Finset.prod_one_add, coeff_mul]

end SpinGlass.SKPrimitiveExpansion
