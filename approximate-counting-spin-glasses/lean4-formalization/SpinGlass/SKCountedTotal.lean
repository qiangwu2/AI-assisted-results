import SpinGlass.SKCountedControl

/-! Complete counted schedule: numerical arithmetic, structural comparisons,
register indexing, finite uniform draws, and candidate traversal. -/
noncomputable section
namespace SpinGlass.SKCountedExecution
open scoped BigOperators
open ArithmeticEvaluation
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The arithmetic trial supplemented by its full conservative structural and
sampling schedule. Its numerical computation is unchanged. -/
def totalTrial {L : ℕ} (A : Finset V) (χ : SKActualEvaluator.Outside A → Fin L)
    (f : Finset V → ℝ) : Computation :=
  let prim := primitives (SKActualEvaluator.branch A) Subtype.val χ f
  let es := (SKFastEvaluator.directPairs A.card).toList.map
    (fun p => (SKFastEvaluator.direct (L := L) (SKActualEvaluator.branch A) f p.1 p.2).coeff)
  let result := trial A χ f
  ⟨result.value, result.operations + outerTrialControl (W := SKActualEvaluator.Outside A)
    (Fintype.card V) A.card L + SKCountedAlgebra.expControl A.card L L +
    SKCountedAlgebra.directControl es⟩

@[simp] theorem totalTrial_value {L : ℕ} (A : Finset V)
    (χ : SKActualEvaluator.Outside A → Fin L) (f : Finset V → ℝ) :
    (totalTrial A χ f).value = (trial A χ f).value := rfl

theorem totalTrial_operations_le {L : ℕ} (A : Finset V)
    (χ : SKActualEvaluator.Outside A → Fin L) (f : Finset V → ℝ) :
    (totalTrial A χ f).operations ≤ 512 * (Fintype.card V+L+1)^6 * 4^L * 36^A.card := by
  let prim := primitives (SKActualEvaluator.branch A) Subtype.val χ f
  let es := (SKFastEvaluator.directPairs A.card).toList.map
    (fun p => (SKFastEvaluator.direct (L := L) (SKActualEvaluator.branch A) f p.1 p.2).coeff)
  have hb := Finset.card_le_univ A
  have hw : Fintype.card (SKActualEvaluator.Outside A) ≤ Fintype.card V := Fintype.card_subtype_le _
  have ho := outerTrialControl_bound (L := L) hb hw
  have he : es.length ≤ A.card^2 := by simpa [es] using SKOperationCount.directPairs_card_le A.card
  have ha := SKCountedAlgebra.totalEvaluatorWork_bound hb prim.value es he
  have ht := trial_operations_le A χ f
  have hpow : (Fintype.card V+L+1)^4 ≤ (Fintype.card V+L+1)^6 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have htt : (trial A χ f).operations ≤ 32*(Fintype.card V+L+1)^6*4^L*36^A.card := by
    apply ht.trans
    gcongr
  change (trial A χ f).operations + _ + _ + SKCountedAlgebra.directControl es ≤ _
  unfold SKCountedAlgebra.totalEvaluatorWork at ha
  nlinarith

/-- Trial averaging propagates both arithmetic and structural counters. -/
def totalAverage (L R : ℕ) (A : Finset V) (χ : Fin R → V → Fin L)
    (f : Finset V → ℝ) : Computation :=
  mul (InputPreparation.divide (literal 1) (literal (R : ℝ)))
    (sumFinset Finset.univ (fun r => totalTrial A (fun v => χ r v.val) f))

/-- Candidate generation/control is charged once per generated candidate, and
one terminating traversal test is charged. No unvisited colors are drawn. -/
def totalEstimator (D L R : ℕ) (χ : Finset V → Fin R → V → Fin L)
    (f : Finset V → ℝ) : Counted ℝ :=
  let result := sumFinset (candidates V D) (fun A => totalAverage L R A (χ A) f)
  ⟨result.value, result.operations +
    visitControl (20 * (Fintype.card V+L+1)^2) (candidates V D).toList⟩

@[simp] theorem totalEstimator_value (D L R : ℕ)
    (χ : Finset V → Fin R → V → Fin L) (f : Finset V → ℝ) :
    (totalEstimator D L R χ f).value = SKActualEvaluator.estimator D L R χ f := by
  simp only [totalEstimator, sumFinset_value, totalAverage, mul, InputPreparation.divide, literal, one_div,
    totalTrial_value, trial_value, SKActualEvaluator.estimator]
  exact sum_candidates D _

/-- Total operations, including comparisons and finite uniform draws, have a
single fixed polynomial exponent, uniformly in every cutoff and input. -/
theorem totalEstimator_operations_le (D L R : ℕ) (hR : 0 < R)
    (χ : Finset V → Fin R → V → Fin L) (f : Finset V → ℝ) :
    (totalEstimator D L R χ f).operations ≤
      2048 * R * (Fintype.card V+L+1)^6 * 4^L *
        (∑ b ∈ Finset.range (D+1), (Fintype.card V).choose b * 36^b) := by
  let M := Fintype.card V+L+1
  let P := M^6*4^L
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hP : 1 ≤ P := Nat.succ_le_of_lt (by dsimp [P]; positivity)
  have hM2 : M^2 ≤ P := by
    calc
      M^2 ≤ M^6 := Nat.pow_le_pow_right hM (by omega)
      _ ≤ M^6*4^L := Nat.le_mul_of_pos_right _ (by positivity)
  have hlocal (A : Finset V) : (totalAverage L R A (χ A) f).operations + 1 + 20*M^2 + 1 ≤
      2048*R*P*36^A.card := by
    have ht : (∑ r : Fin R, (totalTrial A (fun v => χ A r v.val) f).operations) ≤
        R*(512*P*36^A.card) := by
      calc
        _ ≤ ∑ _r : Fin R, (512*P*36^A.card) :=
          Finset.sum_le_sum (fun r _ => by simpa [P, M, Nat.mul_assoc] using totalTrial_operations_le A (fun v => χ A r v.val) f)
        _ = _ := by simp
    have hpow : 1 ≤ 36^A.card := Nat.succ_le_of_lt (by positivity)
    have hm : R ≤ R*P*36^A.card := by
      calc
        R ≤ R*P := Nat.le_mul_of_pos_right _ (by positivity)
        _ ≤ R*P*36^A.card := Nat.le_mul_of_pos_right _ (by positivity)
    have hsmall : M^2 ≤ R*P*36^A.card := by
      calc
        M^2 ≤ P := hM2
        _ ≤ R*P := Nat.le_mul_of_pos_left _ hR
        _ ≤ R*P*36^A.card := Nat.le_mul_of_pos_right _ (by positivity)
    simp only [totalAverage, mul, InputPreparation.divide, literal, one_div, sumFinset_operations, Finset.card_univ, Fintype.card_fin]
    nlinarith
  have hc : 1 ≤ (candidates V D).card := by
    apply Finset.card_pos.mpr
    exact ⟨∅, by simp⟩
  have hsum := Finset.sum_le_sum (s := candidates V D) (fun A _ => hlocal A)
  have hsumR : (∑ A ∈ candidates V D, 2048*R*P*36^A.card) =
      2048*R*P*(∑ b ∈ Finset.range (D+1), (Fintype.card V).choose b*36^b) := by
    rw [← Finset.mul_sum, sum_candidates_card]
  rw [hsumR] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at hsum
  simp only [totalEstimator, sumFinset_operations, visitControl_eq, Finset.length_toList]
  change _ ≤ 2048*R*M^6*4^L*_
  have heq : 2048*R*P = 2048*R*M^6*4^L := by dsimp [P]; ring
  rw [heq] at hsum
  change _ + (1 + (candidates V D).card * (20*M^2)) ≤ _
  omega

end SpinGlass.SKCountedExecution
