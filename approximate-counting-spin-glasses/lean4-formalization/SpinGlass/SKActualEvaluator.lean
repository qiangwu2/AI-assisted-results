import SpinGlass.SKFastEvaluator
import SpinGlass.ColoringProbability
import SpinGlass.SKBranchingBridge
import Mathlib.Data.Fintype.EquivFin

/-!
# Canonical finite-vertex instantiation of Algorithm 5

Branch labels are the actual elements of the candidate set, outside labels are
its complement, and the signed input is indexed by unordered edges. No primitive
specification or evaluator-correctness premise is accepted by these definitions.
-/

noncomputable section
namespace SpinGlass.SKActualEvaluator

open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite labeling of precisely the selected branch vertices. -/
def branch (A : Finset V) (a : Fin A.card) : V := (A.equivFin.symm a).val

/-- The actual outside-vertex type. -/
abbrev Outside (A : Finset V) := {v : V // v ∉ A}

theorem branch_injective (A : Finset V) : Function.Injective (branch A) := by
  intro a b h
  apply A.equivFin.symm.injective
  exact Subtype.ext h

@[simp] theorem branch_mem (A : Finset V) (a : Fin A.card) : branch A a ∈ A :=
  (A.equivFin.symm a).property

/-- The chosen labels exhaust the candidate set exactly. -/
theorem branch_range (A : Finset V) (v : V) : v ∈ A ↔ ∃ a, branch A a = v := by
  constructor
  · intro hv
    exact ⟨A.equivFin ⟨v, hv⟩, by simp [branch]⟩
  · rintro ⟨a, rfl⟩
    exact branch_mem A a

theorem outside_injective (A : Finset V) : Function.Injective (Subtype.val : Outside A → V) :=
  Subtype.val_injective

theorem branch_ne_outside (A : Finset V) (a : Fin A.card) (v : Outside A) :
    branch A a ≠ v.val := by
  intro h
  exact v.property (h ▸ branch_mem A a)

/-- A total ambient color map extending the outside coloring; branch colors are
unused by the graph algebra and may be fixed to the first available color. -/
def totalColor {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L) : V → Fin L :=
  fun v => if hv : v ∉ A then χ ⟨v, hv⟩ else ⟨0, hL⟩

@[simp] theorem totalColor_outside {L : ℕ} (A : Finset V)
    (χ : Outside A → Fin L) (hL : 0 < L) (v : Outside A) :
    totalColor A χ hL v.val = χ v := by simp [totalColor, v.property]

/-- Concrete Algorithm 5 on a fixed candidate set and coloring of its outside vertices. -/
def evaluate {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (f : Finset V → ℝ) :
    SKCoefficient.Coefficients A.card L :=
  SKFastEvaluator.evaluate (branch A) Subtype.val χ f

/-- The output coefficient in equation (75), using actual vertex sets. -/
def coefficient {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (f : Finset V → ℝ)
    (k : Fin (L + 1)) (S : Finset (Fin L)) : ℝ :=
  evaluate A χ f (SKGraphMonomial.target k S)

/-- The returned vector in equation (77). -/
def byOutsideSize {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (f : Finset V → ℝ) (m : ℕ) : ℝ :=
  SKFastEvaluator.byOutsideSize (branch A) Subtype.val χ f m

/-- Actual finite Algorithm 2 aggregation of Algorithm 5 calls, with the displayed
inverse color probability, repetitions, and all candidate branch sets. -/
def estimator (D L R : ℕ) (χ : Finset V → Fin R → V → Fin L)
    (f : Finset V → ℝ) : ℝ :=
  ∑ b ∈ Finset.range (D + 1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b,
    (R : ℝ)⁻¹ * ∑ r : Fin R, ∑ m ∈ Finset.range (L + 1),
      (ColoringProbability.probability L m)⁻¹ *
        byOutsideSize A (fun v => χ A r v.val) f m

/-- An input for an empty branch set has no branch-pair factors. -/
theorem empty_directPairs : SKFastEvaluator.directPairs 0 = ∅ := by
  simp [SKFastEvaluator.directPairs]

/-- Unused vertices outside the support have degree zero, supplying the missing
zero-degree case in the exact branch-state extraction theorem. -/
theorem degree_zero_of_not_outside (A : Finset V) (Γ : Finset (Finset V))
    (v : V) (hvA : v ∉ A) (hv : v ∉ SKGraphMonomial.outside id A Γ) :
    Expansion.degree id Γ v = 0 := by
  unfold Expansion.degree
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heΓ, hve⟩ := Finset.mem_filter.mp he
  exact hv (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨e, heΓ, hve⟩, hvA⟩)

end SpinGlass.SKActualEvaluator
