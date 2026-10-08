import SpinGlass.SKCountedExecutionPrimitives
import SpinGlass.SKActualEvaluator

/-! Saved-array coefficient extraction with one multiplication and addition per
edge-count/color-set pair. -/
noncomputable section
namespace SpinGlass.SKCountedExecution
open scoped BigOperators
open ArithmeticEvaluation SKCoefficient

/-- The already materialized coefficient array is read once at every requested
coordinate; inverse color probabilities are fixed rational constants. -/
def extract {b L : ℕ} (f : Coefficients b L) : Computation :=
  sumFinset Finset.univ (fun p : Fin (L + 1) × Finset (Fin L) =>
    mul (literal (ColoringProbability.probability L p.2.card)⁻¹)
      (literal (f (SKGraphMonomial.target p.1 p.2))))

@[simp] theorem extract_value {b L : ℕ} (f : Coefficients b L) :
    (extract f).value = ∑ m ∈ Finset.range (L + 1),
      (ColoringProbability.probability L m)⁻¹ *
        (∑ k : Fin (L + 1), ∑ S : Finset (Fin L),
          if S.card = m then f (SKGraphMonomial.target k S) else 0) := by
  simp only [extract, sumFinset_value, ArithmeticEvaluation.mul, literal, Fintype.sum_prod_type]
  symm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hm : S.card ∈ Finset.range (L + 1) := Finset.mem_range.mpr
    (Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S))
  simp [mul_ite, hm]

@[simp] theorem extract_operations {b L : ℕ} (f : Coefficients b L) :
    (extract f).operations = 2 * (L + 1) * 2 ^ L := by
  simp [extract, sumFinset_operations, ArithmeticEvaluation.mul, literal, Fintype.card_prod]
  ring

theorem extract_operations_le {b L : ℕ} (f : Coefficients b L) :
    (extract f).operations ≤ 2 * SKOperationCount.registers b L := by
  rw [extract_operations, SKOperationCount.registers]
  have h : 1 ≤ 6 ^ b := Nat.succ_le_of_lt (by positivity)
  simpa only [Nat.mul_assoc, Nat.mul_one] using Nat.mul_le_mul_left (2 * (L + 1) * 2 ^ L) h

end SpinGlass.SKCountedExecution
