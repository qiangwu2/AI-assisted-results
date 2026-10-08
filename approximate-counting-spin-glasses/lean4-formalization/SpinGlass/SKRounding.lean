import SpinGlass.RoundingExecution
import SpinGlass.SKUniformAlgorithm

/-! All integer searches used by the automatically selected SK parameters are
paid for by the final execution schedule. -/
noncomputable section
namespace SpinGlass.SKUniformAlgorithm
open RoundingExecution
open SpinGlass.DesignConstants SpinGlass.AlgorithmBudgets

theorem floorSearch_le_setup {N : ℕ} {B : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) :
    (RoundingExecution.floorSearch N (alpha B)).operations ≤ 10*(N+1) := by
  have h := valid hB hBT
  have hf := RoundingExecution.floorSearch_operations_le N h.alpha_pos.le h.alpha_le
  omega

theorem rounding_search_values (N : ℕ) {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) :
    (RoundingExecution.floorSearch N (alpha B)).value = Nat.floor (alpha B*N) ∧
    (edgeSearch (inflation B) (budget B u)).value = edgeLimit B u ∧
    (repetitionSearch (edgeLimit B u) (budget B u)).value = repetitions B u := by
  have h := valid hB hBT
  simp [h.alpha_pos.le, edgeLimit, repetitions]

theorem rounding_search_cost {N : ℕ} {B u : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) :
    (RoundingExecution.floorSearch N (alpha B)).operations +
      (edgeSearch (inflation B) (budget B u)).operations +
      (repetitionSearch (edgeLimit B u) (budget B u)).operations ≤
        10*(N+edgeLimit B u+repetitions B u+1) := by
  have h := valid hB hBT
  exact all_rounding_operations N h.alpha_pos.le h.alpha_le (inflation B) (budget B u)

end SpinGlass.SKUniformAlgorithm
