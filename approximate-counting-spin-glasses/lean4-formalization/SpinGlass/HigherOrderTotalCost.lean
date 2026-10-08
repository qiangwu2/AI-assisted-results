import SpinGlass.HigherOrderControl

/-! # Full finite-index schedule for the higher-order counting algorithm

The returned value is the proved physical estimator. Its counter adds the
explicit comparison, finite-generation, cached-lookup and control schedules
to the arithmetic/elementary-oracle instructions. There are no random draws
in this deterministic branch of the theorem.
-/
noncomputable section
namespace SpinGlass.HigherOrderTotalCost
open scoped BigOperators
open Finset Real MeasureTheory
open SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation
open SpinGlass.HigherOrderAlgorithm SpinGlass.HigherOrderControl
open SpinGlass.DesignConstants SpinGlass.CountingReduction
open SpinGlass.AccuracyRuntime SpinGlass.PolynomialRuntime
attribute [local instance] Classical.propDecidable

/-- Arithmetic and the finite structural schedules are both included. -/
def countedTotal (p N : ℕ) (B beta epsilon delta : ℝ) (J : Finset (Fin N) → ℝ) : Computation :=
  let arithmetic := countedCount p N B beta epsilon delta J
  let input := prepareInput p beta J
  ⟨arithmetic.value, arithmetic.operations + setupControl p N +
    cachedControl p N B (mseBudget p B epsilon delta) input⟩

@[simp] theorem countedTotal_value (p N : ℕ) (B beta epsilon delta : ℝ)
    (J : Finset (Fin N) → ℝ) :
    (countedTotal p N B beta epsilon delta J).value = (countedCount p N B beta epsilon delta J).value := rfl

theorem cached_arithmetic_le {p N : ℕ} {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hd : 0 < delta) (J : Finset (Fin N) → ℝ) :
    (cachedEvaluator p N B (mseBudget p B epsilon delta) (prepareInput p beta J)).operations ≤
      (countedCount p N B beta epsilon delta J).operations := by
  have hC : 0 < constant p B := lt_of_lt_of_le zero_lt_one (constant_ge_one hB hBT)
  simp only [countedCount, prepareBudget_u hC hd, mseBudget]
  split_ifs <;> simp only [add, literal, logarithm] <;> omega

theorem countedTotal_operations_le {p N : ℕ} {B beta epsilon delta : ℝ}
    (hp : 3 ≤ p) (hpN : p ≤ N) (hB : 0 < B) (hBT : B < betaThreshold p)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1)
    (J : Finset (Fin N) → ℝ) :
    (countedTotal p N B beta epsilon delta J).operations ≤
      600*(N+1)^(2*p+2)*((countedCount p N B beta epsilon delta J).operations+1) := by
  have hu := mseBudget_mem_Ioo hB hBT he he1 hd hd1
  have hc := cachedControl_le (beta := beta) hp hpN hB hBT hu.1 hu.2 J
  have hs := setupControl_le hpN
  have ha := cached_arithmetic_le (beta := beta) (epsilon := epsilon) hB hBT hd J
  let T := (N+1)^2*(N.choose p+1)^2
  have hT : 1 ≤ T := Nat.one_le_of_lt (by dsimp [T]; positivity)
  have hc' : cachedControl p N B (mseBudget p B epsilon delta) (prepareInput p beta J) ≤
      40*T*(countedCount p N B beta epsilon delta J).operations := by
    have hmult := Nat.mul_le_mul_left (40*(N+1)^2*(N.choose p+1)^2) ha
    have ht := hc.trans hmult
    simpa only [T, Nat.mul_assoc] using ht
  have hs' : setupControl p N ≤ 100*T := by simpa [T,Nat.mul_assoc] using hs
  have hwork : (countedTotal p N B beta epsilon delta J).operations ≤
      150*T*((countedCount p N B beta epsilon delta J).operations+1) := by
    unfold countedTotal
    nlinarith [Nat.mul_le_mul_right (countedCount p N B beta epsilon delta J).operations hT]
  have hM : N.choose p ≤ (N+1)^p :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hP : 1 ≤ (N+1)^p := Nat.one_le_pow _ _ (by omega)
  have hM1 : N.choose p+1 ≤ 2*(N+1)^p := by omega
  have hTb : T ≤ 4*(N+1)^(2*p+2) := by
    calc
      T ≤ (N+1)^2*(2*(N+1)^p)^2 := by dsimp [T]; gcongr
      _ = _ := by
        rw [show 2*p+2 = 2+p*2 by omega, pow_add, mul_pow, ← pow_mul]
        ring
  exact hwork.trans (by nlinarith [Nat.mul_le_mul_right ((countedCount p N B beta epsilon delta J).operations+1) hTb])

/-- Correctness is unchanged by charging the actual finite control schedules. -/
theorem counted_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SpinGlass.Disorder.SymmetricLaw μ) (hunit : SpinGlass.Disorder.UnitSecondMoment μ)
    {p N : ℕ} (hp : 3 ≤ p) (hpN : p ≤ N) {B beta epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaThreshold p) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    (SpinGlass.Disorder.iidLaw μ).real {J : Finset (Fin N) → ℝ |
      epsilon < |(countedTotal p N B beta epsilon delta J).value - targetLog p N beta J|} ≤
      remainder μ p N B + delta := by
  simpa only [countedTotal_value] using
    HigherOrderAlgorithm.counted_probability μ hμ hunit hp hpN hB hBT hbeta hbetaB he he1 hd hd1

/-- All finite comparisons, index generation and cached list lookups preserve
the stated common-exponent polynomial, for fixed p and B. -/
theorem counted_polynomial {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), p ≤ N → ∀ (beta epsilon delta : ℝ),
      0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ∀ J : Finset (Fin N) → ℝ,
      ((countedTotal p N B beta epsilon delta J).operations : ℝ) ≤
        C*(N:ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨k,hk,hwork⟩ := HigherOrderAlgorithm.counted_polynomial hp hB hBT
  let d : ℕ := 2*p+2
  let A : ℝ := 600*(2:ℝ)^d*(k+1)
  let C : ℝ := max 1 (max (k+d) A)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hkd : k+(d:ℝ) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hkC : k ≤ C := (by have := (Nat.cast_nonneg d : (0:ℝ) ≤ d); linarith : k ≤ k+(d:ℝ)).trans hkd
  have hAC : A ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro N hpN beta epsilon delta he he1 hd hd1 J
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
  have hNpos : (0:ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hnp : 1 ≤ (N:ℝ)^k := Real.one_le_rpow hN hk.le
  have hep : 1 ≤ epsilon^(-k) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1.le (by linarith)
  have hdp : 1 ≤ delta^(-k) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1.le (by linarith)
  have hprod : 1 ≤ (N:ℝ)^k*epsilon^(-k)*delta^(-k) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hnp hep) hdp
  have harith := hwork N hpN beta epsilon delta he he1 hd hd1 J
  have hplus : ((countedCount p N B beta epsilon delta J).operations : ℝ)+1 ≤
      (k+1)*(N:ℝ)^k*epsilon^(-k)*delta^(-k) := by nlinarith
  have hsize : ((N:ℝ)+1)^d ≤ (2:ℝ)^d*(N:ℝ)^d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hcost : ((countedTotal p N B beta epsilon delta J).operations : ℝ) ≤
      600*((N:ℝ)+1)^d*(((countedCount p N B beta epsilon delta J).operations : ℝ)+1) := by
    exact_mod_cast countedTotal_operations_le hp hpN hB hBT he he1 hd hd1 J
  have hnC := Real.rpow_le_rpow_of_exponent_le hN hkd
  have heC := Real.rpow_le_rpow_of_exponent_ge he he1.le (neg_le_neg hkC)
  have hdC := Real.rpow_le_rpow_of_exponent_ge hd hd1.le (neg_le_neg hkC)
  calc
    _ ≤ 600*((N:ℝ)+1)^d*(((countedCount p N B beta epsilon delta J).operations : ℝ)+1) := hcost
    _ ≤ 600*((2:ℝ)^d*(N:ℝ)^d)*((k+1)*(N:ℝ)^k*epsilon^(-k)*delta^(-k)) := by gcongr
    _ = A*(N:ℝ)^(k+(d:ℝ))*epsilon^(-k)*delta^(-k) := by
      rw [Real.rpow_add hNpos, Real.rpow_natCast]
      dsimp [A]
      ring
    _ ≤ C*(N:ℝ)^C*epsilon^(-C)*delta^(-C) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul hAC hnC (Real.rpow_nonneg hNpos.le _) hC.le
        · exact heC
        · exact (Real.rpow_pos_of_pos he _).le
        · exact mul_nonneg hC.le (Real.rpow_nonneg hNpos.le _)
      · exact hdC
      · exact (Real.rpow_pos_of_pos hd _).le
      · positivity

/-- Probability and the complete comparison/arithmetic finite-index schedule
are certified for the same returned value and a uniform fixed exponent. -/
theorem end_to_end {p : ℕ} {B : ℝ} (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      SpinGlass.Disorder.SymmetricLaw μ → SpinGlass.Disorder.UnitSecondMoment μ →
      ∀ (N : ℕ), p ≤ N → ∀ (beta epsilon delta : ℝ), 0 ≤ beta → beta ≤ B →
        0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ((SpinGlass.Disorder.iidLaw μ).real {J : Finset (Fin N) → ℝ |
        epsilon < |(countedTotal p N B beta epsilon delta J).value - targetLog p N beta J|} ≤
          remainder μ p N B + delta) ∧
      (∀ J : Finset (Fin N) → ℝ, ((countedTotal p N B beta epsilon delta J).operations : ℝ) ≤
        C*(N:ℝ)^C*epsilon^(-C)*delta^(-C)) := by
  obtain ⟨C,hC,hcost⟩ := counted_polynomial hp hB hBT
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N hpN beta epsilon delta hbeta hbetaB he he1 hd hd1
  exact ⟨counted_probability μ hμ hunit hp hpN hB hBT hbeta hbetaB he he1 hd hd1,
    hcost N hpN beta epsilon delta he he1 hd hd1⟩

end SpinGlass.HigherOrderTotalCost
