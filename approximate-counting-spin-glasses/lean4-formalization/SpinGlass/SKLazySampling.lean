import SpinGlass.FiniteUniformMarginals
import SpinGlass.SKCountedGeneration

/-! # Only queried colors need to be drawn

The proof-space color array is restricted to the finite set of candidate,
repetition and outside-vertex positions that the actual evaluator reads. The
resulting law is exactly the product of fresh uniform draws at those positions.
-/
noncomputable section
namespace SpinGlass.SKLazySampling
open MeasureTheory
open scoped BigOperators
open SpinGlass.FiniteProbability SpinGlass.SKCountedExecution
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Position (V : Type*) (R : ℕ) := Finset V × Fin R × V

def usedPositions (D R : ℕ) : Finset (Position V R) :=
  Finset.univ.filter (fun p => p.1 ∈ candidates V D ∧ p.2.2 ∉ p.1)

abbrev Samples (V : Type*) [Fintype V] [DecidableEq V] (D L R : ℕ) :=
  (usedPositions (V := V) D R) → Fin L

/-- Currying only changes the tape's finite representation. -/
def flatten (L R : ℕ) :
    (Finset V → Fin R → V → Fin L) ≃ (Position V R → Fin L) where
  toFun χ p := χ p.1 p.2.1 p.2.2
  invFun ψ A r v := ψ (A,r,v)
  left_inv χ := rfl
  right_inv ψ := by funext p; rcases p with ⟨A,r,v⟩; rfl

def restrict (D L R : ℕ) (χ : Finset V → Fin R → V → Fin L) : Samples V D L R :=
  fun p => χ p.val.1 p.val.2.1 p.val.2.2

/-- Every actual queried coordinate is an independent uniform draw; no colors
for other candidates or for branch vertices are included in this measure. -/
def sampleLaw (D L R : ℕ) : Measure (Samples V D L R) :=
  Measure.pi (fun _ => uniformLaw (Fin L))

theorem restrict_law (D L R : ℕ) (hL : 0 < L) :
    (uniformLaw (Finset V → Fin R → V → Fin L)).map (restrict D L R) =
      sampleLaw (V := V) D L R := by
  letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  have hf : (uniformLaw (Finset V → Fin R → V → Fin L)).map (flatten (V := V) L R) =
      uniformLaw (Position V R → Fin L) := by
    apply uniformLaw_map_of_mean
    intro g
    exact ColorRestriction.mean_equiv (flatten L R) g
  have hm : Measurable (flatten (V := V) L R) := measurable_of_finite _
  have hr : Measurable (fun ψ : Position V R → Fin L => fun p : usedPositions (V := V) D R => ψ p) :=
    measurable_of_finite _
  change (uniformLaw _).map ((fun ψ : Position V R → Fin L =>
    fun p : usedPositions (V := V) D R => ψ p) ∘ flatten L R) = _
  rw [← Measure.map_map hr hm, hf, uniformLaw_restrict]
  exact uniformLaw_pi

/-- Unqueried entries may be filled with any fixed legal color. This completion
is for semantic comparison only and is not part of the sampled input. -/
def complete (D L R : ℕ) (hL : 0 < L) (ξ : Samples V D L R) :
    Finset V → Fin R → V → Fin L :=
  fun A r v => if h : (A,r,v) ∈ usedPositions (V := V) D R then ξ ⟨(A,r,v),h⟩ else ⟨0,hL⟩

@[simp] theorem complete_restrict_outside (D L R : ℕ) (hL : 0 < L)
    (χ : Finset V → Fin R → V → Fin L) (A : Finset V) (hA : A ∈ candidates V D)
    (r : Fin R) (v : SKActualEvaluator.Outside A) :
    complete D L R hL (restrict D L R χ) A r v.val = χ A r v.val := by
  have hc : A.card ≤ D := (mem_candidates D A).mp hA
  simp [complete, usedPositions, hc, v.property, restrict]

/-- The actual program reads only this sampled marginal. Equality holds for
every tape, not merely almost surely. -/
theorem generatedEstimator_complete (D L R : ℕ) (hL : 0 < L)
    (χ : Finset V → Fin R → V → Fin L) (f : Finset V → ℝ) :
    (generatedEstimator D L R (complete D L R hL (restrict D L R χ)) f).value =
      (generatedEstimator D L R χ f).value := by
  rw [generatedEstimator_value, generatedEstimator_value,
    ← totalEstimator_value, ← totalEstimator_value]
  simp only [totalEstimator, ArithmeticEvaluation.sumFinset_value, totalAverage,
    ArithmeticEvaluation.mul, ArithmeticEvaluation.literal, InputPreparation.divide, one_div]
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  funext v
  exact complete_restrict_outside D L R hL χ A hA r v

/-- Exactly one draw per queried position, equivalently one per outside vertex
in each executed candidate/trial. -/
theorem usedPositions_card (D R : ℕ) :
    (usedPositions (V := V) D R).card =
      R * ∑ A ∈ candidates V D, samplingDraws A := by
  simp only [usedPositions, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  simp_rw [show ∀ A : Finset V, ∀ v : V,
    (if A ∈ candidates V D ∧ v ∉ A then 1 else 0 : ℕ) =
      if A ∈ candidates V D then (if v ∉ A then 1 else 0) else 0 by
        intro A v; by_cases hA : A ∈ candidates V D <;> by_cases hv : v ∈ A <;> simp [hA,hv]]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  simp only [Finset.sum_boole, ← Fintype.card_subtype, ← samplingDraws_eq]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.mul_sum]
  simp only [Nat.cast_id]

/-- The restricted law is independent of the disorder input, exactly as the
full proof-space tape was. -/
theorem restrict_joint_law {X : Type*} [MeasurableSpace X] (P : Measure X) [SFinite P]
    (D L R : ℕ) (hL : 0 < L) :
    ((uniformLaw (Finset V → Fin R → V → Fin L)).prod P).map
      (Prod.map (restrict D L R) id) = (sampleLaw (V := V) D L R).prod P := by
  have hr : MeasurePreserving (restrict (V := V) D L R)
      (uniformLaw (Finset V → Fin R → V → Fin L)) (sampleLaw D L R) :=
    ⟨measurable_of_finite _, restrict_law D L R hL⟩
  exact (hr.prod (MeasurePreserving.id P)).map_eq

/-- Operational lazy program, whose only random input is the queried sample
vector. Completion represents a read accessor with an unused default. -/
def sampledEstimator (D L R : ℕ) (hL : 0 < L) (ξ : Samples V D L R)
    (f : Finset V → ℝ) : Counted ℝ :=
  generatedEstimator D L R (complete D L R hL ξ) f

theorem sampledEstimator_law (D L R : ℕ) (hL : 0 < L) (f : Finset V → ℝ) :
    (uniformLaw (Finset V → Fin R → V → Fin L)).map
      (fun χ => (generatedEstimator D L R χ f).value) =
    (sampleLaw (V := V) D L R).map (fun ξ => (sampledEstimator D L R hL ξ f).value) := by
  rw [← restrict_law D L R hL]
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  apply congrArg (Measure.map · (uniformLaw (Finset V → Fin R → V → Fin L)))
  funext χ
  exact (generatedEstimator_complete D L R hL χ f).symm

/-- Uniform draws can be generated in this explicit bounded-candidate order. -/
def queryList (D R : ℕ) : List (Position V R) :=
  (candidateList V D).flatMap (fun A =>
    (Finset.univ.toList : List (Fin R)).flatMap (fun r =>
      (Finset.univ.toList : List (SKActualEvaluator.Outside A)).map
        (fun v => (A,r,v.val))))

theorem queryList_toFinset (D R : ℕ) :
    (queryList (V := V) D R).toFinset = usedPositions D R := by
  have hmem (A : Finset V) : A ∈ candidateList V D ↔ A ∈ candidates V D := by
    rw [← List.mem_toFinset, candidateList_toFinset]
  ext p
  rcases p with ⟨A,r,v⟩
  simp only [queryList, List.mem_toFinset, List.mem_flatMap, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and, Prod.mk.injEq,
    hmem]
  simp only [usedPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A',hA',r',v',h⟩
    rcases h with ⟨rfl,rfl,rfl⟩
    exact ⟨hA',v'.property⟩
  · rintro ⟨hA,hv⟩
    exact ⟨A,hA,r,⟨v,hv⟩,rfl,rfl,rfl⟩

theorem queryList_length (D R : ℕ) :
    (queryList (V := V) D R).length = R * ∑ A ∈ candidates V D, samplingDraws A := by
  simp only [queryList, List.length_flatMap, List.length_map, Finset.length_toList,
    Finset.card_univ, List.map_const', List.sum_replicate, nsmul_eq_mul,
    Fintype.card_fin, ← samplingDraws_eq]
  rw [candidateList_sum, ← Finset.mul_sum]
  simp only [Nat.cast_id]

theorem queryList_nodup (D R : ℕ) : (queryList (V := V) D R).Nodup := by
  apply (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (queryList (V := V) D R : Multiset (Position V R)))).mp
  change (queryList (V := V) D R).toFinset.card = (queryList (V := V) D R).length
  rw [queryList_toFinset, queryList_length, usedPositions_card]

end SpinGlass.SKLazySampling
