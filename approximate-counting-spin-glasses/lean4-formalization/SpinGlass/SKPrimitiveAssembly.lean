import SpinGlass.SKCatalogSelection
import SpinGlass.SKPrimitiveMonomialValues

/-! # The actual primitive array equals the uniquely indexed graph catalog sum -/
noncomputable section
namespace SpinGlass.SKPrimitiveAssembly
open scoped BigOperators
open SKRing SKGraphMonomial SKFastEvaluator SKActualEvaluator SKCatalogSelection
open SKColorfulCatalog SKPrimitiveMonomials
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The array contribution at one endpoint tag and color subset. -/
def entryArray {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (f : Finset V → ℝ)
    (tag : Tag A.card) (S : Finset (Fin L)) : Element A.card L :=
  match tag with
  | none => if 3 ≤ S.card then
      insertMonomial S.card S (fun _ => 0) (cycleCoefficient Subtype.val χ f S) else 0
  | some (a,c) =>
      if a < c then if 1 ≤ S.card then
        insertMonomial (S.card + 1) S (pathDegrees a c)
          (pathCoefficient (branch A) Subtype.val χ f a c S) else 0
      else if a = c then if 2 ≤ S.card then
        insertMonomial (S.card + 1) S (pathDegrees a a)
          (returnCoefficient (branch A) Subtype.val χ f a S) else 0 else 0

/-- Every computed primitive coefficient is exactly its signed graph-monomial sum. -/
theorem entryArray_eq_sum {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (tag : Tag A.card) (S : Finset (Fin L)) :
    entryArray A χ f tag S =
      ∑ Γ ∈ entry A χ tag S, value id A (branch A) (totalColor A χ hL) f Γ := by
  cases tag with
  | none =>
    simp only [entryArray, entry]
    split
    · exact cycle_sum A χ hL f S (by assumption)
    · simp
  | some p =>
    rcases p with ⟨a,c⟩
    simp only [entryArray, entry]
    split
    next hac =>
      split
      · exact path_sum A χ hL f a c (ne_of_lt hac) S
      · simp
    next hac =>
      split
      next heq =>
        split
        · exact return_sum A χ hL f a S (by assumption)
        · simp
      next heq => simp

/-- Separating diagonal returns and strictly ordered paths introduces no extra factor. -/
theorem entryArray_some_split {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (f : Finset V → ℝ) (a c : Fin A.card) (S : Finset (Fin L)) :
    entryArray A χ f (some (a,c)) S =
      (if a < c then if 1 ≤ S.card then
        insertMonomial (S.card + 1) S (pathDegrees a c)
          (pathCoefficient (branch A) Subtype.val χ f a c S) else 0 else 0) +
      (if a = c then if 2 ≤ S.card then
        insertMonomial (S.card + 1) S (pathDegrees a a)
          (returnCoefficient (branch A) Subtype.val χ f a S) else 0 else 0) := by
  by_cases hac : a < c
  · simp [entryArray, hac, ne_of_lt hac]
  · simp [entryArray, hac]

/-- The recurrence-built polynomial contains exactly one copy of every actual
colorful primitive graph, with its signed weight and true graph coordinates. -/
theorem primitives_eq_catalog {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) :
    primitives (branch A) Subtype.val χ f =
      ∑ Γ ∈ catalog A χ, value id A (branch A) (totalColor A χ hL) f Γ := by
  rw [sum_catalog A χ hL, Fintype.sum_prod_type, Fintype.sum_option]
  simp_rw [← entryArray_eq_sum A χ hL f]
  rw [Fintype.sum_prod_type]
  simp_rw [entryArray_some_split, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [entryArray, primitives, add_assoc]

end SpinGlass.SKPrimitiveAssembly
