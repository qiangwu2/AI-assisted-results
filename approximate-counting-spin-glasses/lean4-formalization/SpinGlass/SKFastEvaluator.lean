import SpinGlass.SKPrimitiveTables
import SpinGlass.SKDenseExecution
import SpinGlass.ColorMemoExecution

/-!
# The actual SK color-subset evaluator

This module instantiates equations (66)--(75) with an explicit branch labeling and
outside-vertex embedding. Every primitive coefficient is computed by the chain
recurrences, and every polynomial product uses the point-update multiplication.
-/

noncomputable section
namespace SpinGlass.SKFastEvaluator

open scoped BigOperators
open SKRing

variable {V W : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]

/-- Ordinary pair weights induced by a signed unordered-edge input array. -/
def pairWeight (f : Finset V → ℝ) (i j : V) : ℝ := f {i, j}

/-- Degree coordinate for an ordinary path between two branch labels. -/
def pathDegrees {b : ℕ} (a c : Fin b) : Fin b → CappedDegree :=
  fun d => CappedDegree.ofNat ((if d = a then 1 else 0) + (if d = c then 1 else 0))

/-- One basis monomial, with the edge-budget test performed before insertion. -/
def insertMonomial {b L : ℕ} (k : ℕ) (S : Finset (Fin L))
    (d : Fin b → CappedDegree) (x : ℝ) : Element b L :=
  if h : k ≤ L then monomial (⟨k, Nat.lt_succ_of_le h⟩, S, d) x else 0

/-- Endpoint closure computed from a saved, completed memo table. -/
def memoClosure {L : ℕ} (χ : W → Fin L) (start : W → ℝ) (w : W → W → ℝ)
    (finish : W → ℝ) (S : Finset (Fin L)) : ℝ :=
  ∑ j, ColorMemoExecution.memo χ start w L S j * finish j

/-- Saved-table execution agrees with the finite-chain semantics. -/
theorem memoClosure_correct {L : ℕ} (χ : W → Fin L) (start : W → ℝ)
    (w : W → W → ℝ) (finish : W → ℝ) (S : Finset (Fin L)) :
    memoClosure χ start w finish S = SKPrimitiveTables.pathClosure χ start w finish S := by
  have hm : ∀ j, ColorMemoExecution.memo χ start w L S j = ColorPath.pathTable χ start w S j :=
    fun j => by simpa using ColorMemoExecution.memo_correct χ start w S j
  simp only [memoClosure, SKPrimitiveTables.pathClosure, hm]

/-- Path closure (66), computed on outside vertices only using saved tables. -/
def pathCoefficient {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (a c : Fin b) (S : Finset (Fin L)) : ℝ :=
  memoClosure χ (fun i => pairWeight f (branch a) (outside i))
    (fun i j => pairWeight f (outside i) (outside j))
    (fun j => pairWeight f (outside j) (branch c)) S

/-- Rooted-cycle coefficient (67), with its two-orientation normalization. -/
def returnCoefficient {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (a : Fin b) (S : Finset (Fin L)) : ℝ :=
  if 2 ≤ S.card then (2 : ℝ)⁻¹ * pathCoefficient branch outside χ f a a S else 0

/-- Entirely outside cycle coefficient (69), normalized by roots and directions. -/
def cycleCoefficient {L : ℕ} (outside : W → V) (χ : W → Fin L)
    (f : Finset V → ℝ) (S : Finset (Fin L)) : ℝ :=
  if 3 ≤ S.card then (2 * S.card : ℝ)⁻¹ *
    ∑ r, memoClosure χ (ColorCycleChain.rootStart r)
      (fun i j => pairWeight f (outside i) (outside j))
      (fun j => pairWeight f (outside j) (outside r)) S else 0

theorem pathCoefficient_eq {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (a c : Fin b) (S : Finset (Fin L)) :
    pathCoefficient branch outside χ f a c S =
      SKPrimitiveTables.pathClosure χ (fun i => pairWeight f (branch a) (outside i))
        (fun i j => pairWeight f (outside i) (outside j))
        (fun j => pairWeight f (outside j) (branch c)) S := memoClosure_correct _ _ _ _ _

theorem returnCoefficient_eq {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (a : Fin b) (S : Finset (Fin L)) :
    returnCoefficient branch outside χ f a S =
      SKPrimitiveTables.rootedClosure χ (fun i => pairWeight f (branch a) (outside i))
        (fun i j => pairWeight f (outside i) (outside j))
        (fun j => pairWeight f (outside j) (branch a)) S := by
  simp only [returnCoefficient, pathCoefficient_eq, SKPrimitiveTables.rootedClosure]

theorem cycleCoefficient_eq {L : ℕ} (outside : W → V) (χ : W → Fin L)
    (f : Finset V → ℝ) (S : Finset (Fin L)) :
    cycleCoefficient outside χ f S =
      SKPrimitiveTables.outsideClosure χ (fun i j => pairWeight f (outside i) (outside j)) S := by
  simp only [cycleCoefficient, memoClosure_correct, SKPrimitiveTables.pathClosure,
    SKPrimitiveTables.outsideClosure, ColorCycleChain.rootTable]

/-- Primitive polynomial (73), constructed from the actual recurrence outputs. -/
def primitives {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) : Element b L :=
  (∑ S : Finset (Fin L), if 3 ≤ S.card then
    insertMonomial S.card S (fun _ => 0) (cycleCoefficient outside χ f S) else 0) +
  (∑ a : Fin b, ∑ c : Fin b, if a < c then
    ∑ S : Finset (Fin L), if 1 ≤ S.card then
      insertMonomial (S.card + 1) S (pathDegrees a c)
        (pathCoefficient branch outside χ f a c S) else 0 else 0) +
  (∑ a : Fin b, ∑ S : Finset (Fin L), if 2 ≤ S.card then
    insertMonomial (S.card + 1) S (pathDegrees a a)
      (returnCoefficient branch outside χ f a S) else 0)

/-- The direct edge factor includes no outside color. -/
def direct {b L : ℕ} (branch : Fin b → V) (f : Finset V → ℝ) (a c : Fin b) : Element b L :=
  insertMonomial 1 ∅ (pathDegrees a c) (pairWeight f (branch a) (branch c))

/-- Each unordered branch pair is scheduled once, by the order of its labels. -/
def directPairs (b : ℕ) : Finset (Fin b × Fin b) := Finset.univ.filter (fun p => p.1 < p.2)

/-- Point-update Algorithm 5 before coefficient extraction. -/
def evaluate {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) : SKCoefficient.Coefficients b L :=
  SKDenseExecution.evaluator (primitives branch outside χ f).coeff
    ((directPairs b).toList.map (fun p => (direct (L := L) branch f p.1 p.2).coeff))

/-- The output coordinate specified in equation (75). -/
def coefficient {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (k : Fin (L + 1)) (S : Finset (Fin L)) : ℝ :=
  evaluate branch outside χ f (SKGraphMonomial.target k S)

/-- Returned graph-weight totals grouped by outside-support size, equation (77). -/
def byOutsideSize {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) (m : ℕ) : ℝ :=
  ∑ k : Fin (L + 1), ∑ S : Finset (Fin L),
    if S.card = m then coefficient branch outside χ f k S else 0

/-- Every inserted nonempty-color monomial lies in the actual color ideal. -/
theorem insertMonomial_vanishesBelow {b L : ℕ} (k : ℕ) (S : Finset (Fin L))
    (d : Fin b → CappedDegree) (x : ℝ) (hS : S.Nonempty) :
    SKCoefficient.VanishesBelow 1 (insertMonomial k S d x).coeff := by
  unfold insertMonomial
  split
  · exact SKPrimitiveExpansion.monomial_vanishesBelow _ _ hS
  · intro z hz
    rfl

/-- Color-ideal membership is preserved by addition. -/
theorem vanishesBelow_add {b L : ℕ} (x y : Element b L)
    (hx : SKCoefficient.VanishesBelow 1 x.coeff)
    (hy : SKCoefficient.VanishesBelow 1 y.coeff) :
    SKCoefficient.VanishesBelow 1 (x + y).coeff := by
  intro z hz
  change x.coeff z + y.coeff z = 0
  rw [hx z hz, hy z hz, add_zero]

/-- The actual recurrence-built primitive polynomial is nilpotent for every signed input. -/
theorem primitives_vanishesBelow {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) :
    SKCoefficient.VanishesBelow 1 (primitives branch outside χ f).coeff := by
  unfold primitives
  apply vanishesBelow_add
  · apply vanishesBelow_add
    · apply SKPrimitiveExpansion.sum_vanishesBelow
      intro S hS
      split
      · apply insertMonomial_vanishesBelow
        exact Finset.card_pos.mp (by omega)
      · intro z hz; rfl
    · apply SKPrimitiveExpansion.sum_vanishesBelow
      intro a ha
      apply SKPrimitiveExpansion.sum_vanishesBelow
      intro c hc
      split
      · apply SKPrimitiveExpansion.sum_vanishesBelow
        intro S hS
        split
        · apply insertMonomial_vanishesBelow
          exact Finset.card_pos.mp (by omega)
        · intro z hz; rfl
      · intro z hz; rfl
  · apply SKPrimitiveExpansion.sum_vanishesBelow
    intro a ha
    apply SKPrimitiveExpansion.sum_vanishesBelow
    intro S hS
    split
    · apply insertMonomial_vanishesBelow
      exact Finset.card_pos.mp (by omega)
    · intro z hz; rfl

/-- The scheduled implementation computes exactly polynomial (74) for its computed primitives. -/
theorem evaluate_eq_polynomial {b L : ℕ} (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) :
    evaluate branch outside χ f =
      (IsNilpotent.exp (primitives branch outside χ f) *
        ∏ p ∈ directPairs b, (1 + direct (L := L) branch f p.1 p.2)).coeff := by
  rw [evaluate, SKDenseExecution.evaluator_correct, SKExponential.algebraEvaluator,
    SKExponential.directLoop_correct,
    SKPrimitiveExpansion.loop_eq_exp _ (primitives_vanishesBelow branch outside χ f)]
  have hd := SKPrimitiveExpansion.directProduct_eq
    ((directPairs b).toList.map (fun p => direct (L := L) branch f p.1 p.2))
  simp only [List.map_map, Function.comp_def, Finset.prod_map_toList] at hd
  rw [hd, coeff_mul]

end SpinGlass.SKFastEvaluator
