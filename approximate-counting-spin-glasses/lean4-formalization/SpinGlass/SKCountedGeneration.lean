import SpinGlass.SKCountedTotal
import SpinGlass.FiniteIndexCosts

/-! The bounded candidate family is realized by the actual pruned combination
list generator; its construction work is covered by the total schedule. -/
noncomputable section
namespace SpinGlass.SKCountedExecution
open scoped BigOperators
open FiniteIndexCosts
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The concrete generator runs only the admissible cardinality layers. -/
def candidateList (V : Type*) [Fintype V] [DecidableEq V] (D : ℕ) : List (Finset V) :=
  (Finset.range (min D (Fintype.card V)+1)).toList.flatMap
    (fun b => chosenFinsets b (Finset.univ : Finset V).toList)

@[simp] theorem candidateList_toFinset (D : ℕ) :
    (candidateList V D).toFinset = candidates V D := by
  ext A
  simp only [candidateList, List.mem_toFinset, List.mem_flatMap, Finset.mem_toList]
  simp_rw [← List.mem_toFinset,
    chosenFinsets_toFinset _ _ (Finset.univ : Finset V).nodup_toList, Finset.toList_toFinset]
  simp only [candidates, Finset.mem_biUnion]

theorem sum_flatMap {I M : Type*} [AddCommMonoid M] (xs : List I) (f : I → List M) :
    (xs.flatMap f).sum = (xs.map (fun i => (f i).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih]

/-- The concrete list and finite-set families have the same scalar folds. -/
theorem candidateList_sum {M : Type*} [AddCommMonoid M] (D : ℕ) (f : Finset V → M) :
    ((candidateList V D).map f).sum = ∑ A ∈ candidates V D, f A := by
  simp only [candidateList, List.map_flatMap, sum_flatMap]
  simp_rw [chosenFinsets_sum]
  rw [Finset.sum_map_toList]
  rw [← sum_candidates]
  congr 1
  ext A
  simp only [mem_candidates]
  have := Finset.card_le_univ A
  omega

/-- Generation work includes recursive pruning and append/map, as well as an
extra quadratic allowance per generated finite set for index conversion. -/
def candidateGenerationWork (N D : ℕ) : ℕ :=
  (min D N + 1) + ∑ b ∈ Finset.range (min D N+1),
    (chooseWork N b + (N+1)^2 * N.choose b)

theorem candidateGenerationWork_le (D L : ℕ) :
    candidateGenerationWork (Fintype.card V) D ≤
      visitControl (20 * (Fintype.card V+L+1)^2) (candidates V D).toList := by
  let N := Fintype.card V
  have hgen := bounded_choose_work (n := N) (cutoff := min D N) (Nat.min_le_right _ _)
  have hcount : (∑ b ∈ Finset.range (min D N+1), N.choose b) = (candidates V D).card := by
    have h := sum_candidates_card (V := V) (min D N) (fun _ => 1)
    have heq : candidates V (min D N) = candidates V D := by
      ext A
      simp only [mem_candidates]
      have := Finset.card_le_univ A
      dsimp [N] at *
      omega
    simpa only [heq, Finset.sum_const, nsmul_eq_mul, Nat.mul_one, Nat.cast_id, N] using h.symm
  have hsteps : min D N+1 ≤ ∑ b ∈ Finset.range (min D N+1), N.choose b := by
    calc
      _ = ∑ _b ∈ Finset.range (min D N+1), (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b hb => Nat.choose_pos (by have := Finset.mem_range.mp hb; omega))
  have hsize : (N+1)^2 ≤ (N+L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hpos : 1 ≤ (N+L+1)^2 := Nat.succ_le_of_lt (by positivity)
  unfold candidateGenerationWork
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [visitControl_eq, Finset.length_toList]
  change _ ≤ 1 + (candidates V D).card * (20*(N+L+1)^2)
  rw [hcount] at hgen hsteps ⊢
  nlinarith

/-- The total estimator's numerical value can be computed by the generated list
itself; no full powerset scan or deduplication is needed. -/
theorem totalEstimator_value_generated (D L R : ℕ)
    (χ : Finset V → Fin R → V → Fin L) (f : Finset V → ℝ) :
    (totalEstimator D L R χ f).value =
      (ArithmeticEvaluation.sumList ((candidateList V D).map
        (fun A => totalAverage L R A (χ A) f))).value := by
  simp only [totalEstimator, ArithmeticEvaluation.sumFinset_value,
    ArithmeticEvaluation.sumList_value, List.map_map, Function.comp_def]
  exact (candidateList_sum D _).symm

@[simp] theorem candidateList_length (D : ℕ) :
    (candidateList V D).length = (candidates V D).card := by
  simpa using candidateList_sum (V := V) D (fun _ => (1 : ℕ))

theorem candidateList_nodup (D : ℕ) : (candidateList V D).Nodup := by
  apply (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (candidateList V D : Multiset (Finset V)))).mp
  change (candidateList V D).toFinset.card = (candidateList V D).length
  rw [candidateList_toFinset, candidateList_length]

/-- The final scheduled program actually uses the pruned generated candidate
list; its generation cost, arithmetic, controls and draws are all included. -/
def generatedEstimator (D L R : ℕ)
    (χ : Finset V → Fin R → V → Fin L) (f : Finset V → ℝ) : Counted ℝ :=
  let result := ArithmeticEvaluation.sumList ((candidateList V D).map
    (fun A => totalAverage L R A (χ A) f))
  ⟨result.value, result.operations + candidateGenerationWork (Fintype.card V) D⟩

@[simp] theorem generatedEstimator_value (D L R : ℕ)
    (χ : Finset V → Fin R → V → Fin L) (f : Finset V → ℝ) :
    (generatedEstimator D L R χ f).value = SKActualEvaluator.estimator D L R χ f := by
  change (ArithmeticEvaluation.sumList _).value = _
  rw [← totalEstimator_value_generated]
  exact totalEstimator_value D L R χ f

theorem generatedEstimator_operations_le (D L R : ℕ) (hR : 0 < R)
    (χ : Finset V → Fin R → V → Fin L) (f : Finset V → ℝ) :
    (generatedEstimator D L R χ f).operations ≤
      2048 * R * (Fintype.card V+L+1)^6 * 4^L *
        (∑ b ∈ Finset.range (D+1), (Fintype.card V).choose b * 36^b) := by
  apply LE.le.trans _ (totalEstimator_operations_le D L R hR χ f)
  simp only [generatedEstimator, totalEstimator, ArithmeticEvaluation.sumList_operations,
    ArithmeticEvaluation.sumFinset_operations, List.map_map, Function.comp_def, List.length_map,
    candidateList_length, candidateList_sum]
  exact Nat.add_le_add_left (candidateGenerationWork_le D L) _

end SpinGlass.SKCountedExecution
