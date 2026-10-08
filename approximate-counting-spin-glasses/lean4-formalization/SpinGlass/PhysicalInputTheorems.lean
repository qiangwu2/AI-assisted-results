import SpinGlass.PhysicalObservables

/-! End-to-end guarantees on exactly the physical iid p-edge input law. -/
noncomputable section
namespace SpinGlass.PhysicalInput
open MeasureTheory
open SpinGlass.Disorder SpinGlass.DesignConstants SpinGlass.CountingReduction

/-- Counted randomized SK program accepting only genuine two-vertex inputs. -/
def skCount (N : ℕ) (B beta epsilon delta : ℝ)
    (hB : 0 < B) (hBT : B < betaThreshold 2) (hd : 0 < delta)
    (χ : SKUniformAlgorithm.Randomness N B (mseBudget 2 B epsilon delta))
    (J : Edge (Fin N) 2 → ℝ) : ArithmeticEvaluation.Computation :=
  SKTotalCost.countedTotal N B beta epsilon delta hB hBT hd χ (extend 2 J)

/-- Counted deterministic higher-order program on its physical input array. -/
def higherCount (p N : ℕ) (B beta epsilon delta : ℝ)
    (J : Edge (Fin N) p → ℝ) : ArithmeticEvaluation.Computation :=
  HigherOrderTotalCost.countedTotal p N B beta epsilon delta (extend p J)

/-- The exact log partition function with its edge-subtype incidence. -/
def physicalTarget (p N : ℕ) (beta : ℝ) (J : Edge (Fin N) p → ℝ) : ℝ :=
  Real.log (Partition.partitionFunction (fun e : Edge (Fin N) p => e.val)
    Finset.univ (fun e => pureScale N p beta * J e))

@[simp] theorem physicalTarget_eq (p N : ℕ) (beta : ℝ) (J : Edge (Fin N) p → ℝ) :
    physicalTarget p N beta J = targetLog p N beta (extend p J) :=
  (targetLog_physical p N beta J).symm

/-- The final probability is exactly unchanged upon dropping all unused
coordinates of the ambient bookkeeping array. -/
theorem sk_event_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold 2) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    ((SKUniformAlgorithm.randomLaw N B (mseBudget 2 B epsilon delta)).prod
      (iidLaw (E := Edge (Fin N) 2) μ)).real
      {χJ | epsilon < |(skCount N B beta epsilon delta hB hBT hd χJ.1 χJ.2).value -
        physicalTarget 2 N beta χJ.2|} =
    ((SKUniformAlgorithm.randomLaw N B (mseBudget 2 B epsilon delta)).prod
      (iidLaw (E := Finset (Fin N)) μ)).real
      {χJ | epsilon < |(SKTotalCost.countedTotal N B beta epsilon delta hB hBT hd χJ.1 χJ.2).value -
        targetLog 2 N beta χJ.2|} := by
  simp only [skCount, physicalTarget_eq]
  apply event_probability _ μ 2 _ (measurable_sk_error_event hB hBT he he1 hd hd1)
  intro χ J
  simp only [Set.mem_setOf_eq, sk_countedTotal_extend_restrict, targetLog_extend_restrict]

theorem higher_event_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hd : 0 < delta) :
    (iidLaw (E := Edge (Fin N) p) μ).real
      {J | epsilon < |(higherCount p N B beta epsilon delta J).value - physicalTarget p N beta J|} =
    (iidLaw (E := Finset (Fin N)) μ).real
      {J | epsilon < |(HigherOrderTotalCost.countedTotal p N B beta epsilon delta J).value -
        targetLog p N beta J|} := by
  simp only [higherCount, physicalTarget_eq]
  apply event_probability_single μ p _ (measurable_higher_error_event hB hBT hd)
  intro J
  simp only [Set.mem_setOf_eq, higher_countedTotal_extend_restrict, targetLog_extend_restrict]

/-- The paper's SK accuracy guarantee under the actual iid pair-edge law. -/
theorem sk_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N : ℕ} (hN : 2 ≤ N)
    {B beta epsilon delta : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    ((SKUniformAlgorithm.randomLaw N B (mseBudget 2 B epsilon delta)).prod
      (iidLaw (E := Edge (Fin N) 2) μ)).real
      {χJ | epsilon < |(skCount N B beta epsilon delta hB hBT hd χJ.1 χJ.2).value -
        physicalTarget 2 N beta χJ.2|} ≤ remainder μ 2 N B + delta := by
  rw [sk_event_probability μ hB hBT he he1 hd hd1]
  exact SKTotalCost.counted_probability μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1

/-- The paper's higher-order accuracy guarantee under the actual iid p-edge law. -/
theorem higher_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {p N : ℕ} (hp : 3 ≤ p) (hpN : p ≤ N)
    {B beta epsilon delta : ℝ} (hB : 0 < B) (hBT : B < betaThreshold p)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hd : 0 < delta) (hd1 : delta < 1) :
    (iidLaw (E := Edge (Fin N) p) μ).real
      {J | epsilon < |(higherCount p N B beta epsilon delta J).value - physicalTarget p N beta J|} ≤
      remainder μ p N B + delta := by
  rw [higher_event_probability μ hB hBT hd]
  exact HigherOrderTotalCost.counted_probability μ hμ hunit hp hpN hB hBT hbeta hbetaB he he1 hd hd1

/-- Full physical-input SK theorem: one fixed polynomial bounds all requested
accuracies, and the real iid probability bound is the original one. -/
theorem sk_end_to_end {B : ℝ} (hB : 0 < B) (hBT : B < betaThreshold 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (N : ℕ), 2 ≤ N →
      ∀ (beta epsilon delta : ℝ), 0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
      ∀ hd : 0 < delta, delta < 1 →
      (((SKUniformAlgorithm.randomLaw N B (mseBudget 2 B epsilon delta)).prod
        (iidLaw (E := Edge (Fin N) 2) μ)).real
        {χJ | epsilon < |(skCount N B beta epsilon delta hB hBT hd χJ.1 χJ.2).value -
          physicalTarget 2 N beta χJ.2|} ≤ remainder μ 2 N B + delta) ∧
      (∀ χ J, ((skCount N B beta epsilon delta hB hBT hd χ J).operations : ℝ) ≤
        C*(N:ℝ)^C*epsilon^(-C)*delta^(-C)) := by
  obtain ⟨C,hC,hcost⟩ := SKTotalCost.counted_polynomial hB hBT
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N hN beta epsilon delta hbeta hbetaB he he1 hd hd1
  exact ⟨sk_probability μ hμ hunit hN hB hBT hbeta hbetaB he he1 hd hd1,
    fun χ J => hcost N hN beta epsilon delta he he1 hd hd1 χ (extend 2 J)⟩

theorem higher_end_to_end {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (N : ℕ), p ≤ N →
      ∀ (beta epsilon delta : ℝ), 0 ≤ beta → beta ≤ B → 0 < epsilon → epsilon < 1 →
      0 < delta → delta < 1 →
      ((iidLaw (E := Edge (Fin N) p) μ).real
        {J | epsilon < |(higherCount p N B beta epsilon delta J).value -
          physicalTarget p N beta J|} ≤ remainder μ p N B + delta) ∧
      (∀ J, ((higherCount p N B beta epsilon delta J).operations : ℝ) ≤
        C*(N:ℝ)^C*epsilon^(-C)*delta^(-C)) := by
  obtain ⟨C,hC,hcost⟩ := HigherOrderTotalCost.counted_polynomial hp hB hBT
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N hpN beta epsilon delta hbeta hbetaB he he1 hd hd1
  exact ⟨higher_probability μ hμ hunit hp hpN hB hBT hbeta hbetaB he he1 hd hd1,
    fun J => hcost N hpN beta epsilon delta he he1 hd hd1 (extend p J)⟩

end SpinGlass.PhysicalInput
