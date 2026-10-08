import SpinGlass.AccuracyBudget
import SpinGlass.DisorderUniform
import SpinGlass.DesignConstants

/-! The final logarithmic reduction, with the complete original-disorder
lower-tail theorem discharged and the paper's concrete parameter choices. -/

noncomputable section
namespace SpinGlass.CountingReduction
open MeasureTheory Real
open SpinGlass.Disorder SpinGlass.DesignConstants SpinGlass.UniformMass

def theta (p : ℕ) (B : ℝ) : ℝ := B / inflatedBeta p B
def exponent (p : ℕ) (B : ℝ) : ℝ := (1-Real.sqrt (theta p B))/Real.sqrt (theta p B)
def constant (p : ℕ) (B : ℝ) : ℝ := massConstant p ((inflatedBeta p B)^2)
def mseBudget (p : ℕ) (B epsilon delta : ℝ) : ℝ :=
  SpinGlass.accuracyMSEBudget (constant p B) delta epsilon (exponent p B)
def normalized (p N : ℕ) (beta : ℝ) (J : Finset (Fin N) → ℝ) : ℝ :=
  SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard p)
    (fun e => pureScale N p beta * J e)
def logBase (p N : ℕ) (beta : ℝ) (J : Finset (Fin N) → ℝ) : ℝ :=
  Real.log (SpinGlass.Partition.prefactor (V := Fin N)
    ((Finset.univ : Finset (Fin N)).powersetCard p) (fun e => pureScale N p beta * J e))
def targetLog (p N : ℕ) (beta : ℝ) (J : Finset (Fin N) → ℝ) : ℝ :=
  Real.log (SpinGlass.Partition.partitionFunction id
    ((Finset.univ : Finset (Fin N)).powersetCard p) (fun e => pureScale N p beta * J e))
def remainder (μ : Measure ℝ) (p N : ℕ) (B : ℝ) : ℝ :=
  disorderTailRemainder μ ((Finset.univ : Finset (Fin N)).powersetCard p)
    (pureScale N p B) (theta p B)

theorem exponent_pos {p : ℕ} {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    0 < exponent p B := by
  have hplus := (inflatedBeta_admissible hB hBT).1
  have hp0 := hB.trans hplus
  exact SpinGlass.LowerTail.negativeExponent_pos (div_pos hB hp0) ((div_lt_one hp0).mpr hplus)

theorem constant_ge_one {p : ℕ} {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p) :
    1 ≤ constant p B :=
  one_le_massConstant (sq_nonneg _) (inflatedBeta_admissible hB hBT).2

theorem mseBudget_mem_Ioo {p : ℕ} {B epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) : 0 < mseBudget p B epsilon delta ∧ mseBudget p B epsilon delta < 1 := by
  have hC := constant_ge_one hB hBT
  exact ⟨SpinGlass.accuracyMSEBudget_pos (by linarith) hd he,
    SpinGlass.accuracyMSEBudget_lt_one hC hd hd1 he he1 (exponent_pos hB hBT)⟩

theorem targetLog_decomposition (p N : ℕ) (beta : ℝ) (J : Finset (Fin N) → ℝ) :
    targetLog p N beta J = logBase p N beta J + Real.log (normalized p N beta J) :=
  SpinGlass.Partition.log_partition_decomposition _ _ _

/-- Only the algorithm MSE and its integrability remain as premises here.
The lower-tail estimate and all scalar substitutions are actual proved results. -/
theorem probability_of_mse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {B beta epsilon delta : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) (T : (Finset (Fin N) → ℝ) → ℝ)
    (hE : Integrable (fun J => (T J - normalized p N beta J)^2) (iidLaw μ))
    (hmse : (∫ J, (T J - normalized p N beta J)^2 ∂iidLaw μ) ≤ mseBudget p B epsilon delta) :
    (iidLaw μ).real {J | epsilon < |SpinGlass.logOutput (logBase p N beta J) (T J) - targetLog p N beta J|} ≤
      remainder μ p N B + delta := by
  have hC := constant_ge_one hB hBT
  have hC0 : 0 < constant p B := by linarith
  have hs := exponent_pos hB hBT
  have hz := SpinGlass.accuracyThreshold_pos (s := exponent p B) hC0 hd
  have hz1 := SpinGlass.accuracyThreshold_lt_one hC hd hd1 hs
  have hplus := inflatedBeta_admissible hB hBT
  have htail := pure_p_spin_lower_tail_uniform_temperature μ hμ hunit hp hpN hbeta hbetaB hB
    hplus.1 hplus.2 hz hz1.le
  simp_rw [targetLog_decomposition]
  apply SpinGlass.logOutput_probability_with_paper_parameters (iidLaw μ)
    (logBase p N beta) T (normalized p N beta) hE hC0 hd he he1.le hs _ hmse
  simpa only [normalized, constant, exponent, theta, remainder, add_comm] using htail

end SpinGlass.CountingReduction
