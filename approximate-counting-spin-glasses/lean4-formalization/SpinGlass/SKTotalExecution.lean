import SpinGlass.SKTheorem
import SpinGlass.SKCountedGeneration
import SpinGlass.HigherOrderControl
import SpinGlass.SKRounding

/-! # Complete SK schedule, including finite controls and color sampling -/
noncomputable section
namespace SpinGlass.SKTotalCost
open Finset Real MeasureTheory
open SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation SpinGlass.SupportEvaluation
open SpinGlass.DesignConstants SpinGlass.CountingReduction SpinGlass.AlgorithmBudgets
open SpinGlass.PolynomialRuntime SpinGlass.SKUniformAlgorithm
attribute [local instance] Classical.propDecidable

/-- The exact branch traverses the Boolean cube; the approximate branch uses
actual generated candidates and its counted sampled-color tables. The final
allowance covers the comparison/increment construction of L and R. -/
def cachedTotal (N : ℕ) (B u : ℝ) (χ : Randomness N B u)
    (input : PreparedInput (Fin N)) : Computation :=
  if exactBranch N B u then
    let r := exactEvaluator 2 (preparedWeight input)
    ⟨r.value, r.operations + HigherOrderControl.localControl input (univ.powersetCard 2) univ⟩
  else
    let r := SKCountedExecution.generatedEstimator (selectedSize N B u-1)
      (edgeLimit B u) (repetitions B u) χ (preparedWeight input)
    ⟨r.value, r.operations + 100*(N+edgeLimit B u+repetitions B u+1)⟩

/-- The integer-search implementations compute precisely the specification's
parameters, and fit the allowance in the approximate branch. -/
theorem rounding_allowance {N : ℕ} {B u : ℝ}
    (hB : 0<B) (hBT : B<betaThreshold 2) :
    (RoundingExecution.floorSearch N (alpha B)).operations+
      (RoundingExecution.edgeSearch (inflation B) (budget B u)).operations+
      (RoundingExecution.repetitionSearch (edgeLimit B u) (budget B u)).operations ≤
        100*(N+edgeLimit B u+repetitions B u+1) := by
  exact (rounding_search_cost hB hBT).trans (by omega)

theorem cachedTotal_value (N : ℕ) (B u : ℝ) (χ : Randomness N B u)
    (input : PreparedInput (Fin N)) :
    (cachedTotal N B u χ input).value = (cachedEvaluator N B u χ input).value := by
  unfold cachedTotal cachedEvaluator
  split_ifs <;> simp only [SKCountedExecution.generatedEstimator_value,
    SKCountedExecution.estimator_value]

def colorAmplitude (B : ℝ) : ℝ := (sizeFactor B)^6*(2*Real.exp (1+Real.log 4))
def totalAmplitude (B : ℝ) : ℝ := 81*amplitude B+4096*colorAmplitude B+1000

theorem amplitude_pos {B : ℝ} (hB : 0<B) (hBT : B<betaThreshold 2) : 0<amplitude B := by
  have := amplitude_ge_exact hB hBT
  have : 0 < 8*(2:ℝ)^(sizeLimit B) := by positivity
  linarith

theorem totalAmplitude_pos {B : ℝ} (hB : 0<B) (hBT : B<betaThreshold 2) : 0<totalAmplitude B := by
  have := amplitude_pos hB hBT
  have : 0<colorAmplitude B := by have := sizeFactor_pos hB hBT; unfold colorAmplitude; positivity
  unfold totalAmplitude
  positivity

theorem approximate_overhead {N L R m : ℕ} (hR : 0<R) (hm : 0<m) :
    100*(N+L+R+1) ≤ 2048*R*(N+L+1)^6*4^L*(∑b∈range m,N.choose b*36^b) := by
  have hsum : 1 ≤ ∑b∈range m,N.choose b*36^b := by
    have h := single_le_sum (f := fun b => N.choose b*36^b)
      (fun b _ => Nat.zero_le _) (mem_range.mpr hm)
    simpa using h
  have hM : 1 ≤ N+L+1 := by omega
  have hM6 : N+L+1 ≤ (N+L+1)^6 := Nat.le_self_pow (by omega) _
  have h4 : 1 ≤ 4^L := Nat.one_le_pow _ _ (by omega)
  have hprod : R*(N+L+1)^6 ≤ R*(N+L+1)^6*4^L*(∑b∈range m,N.choose b*36^b) := by
    nlinarith [Nat.mul_le_mul_left (R*(N+L+1)^6) h4,
      Nat.mul_le_mul_left (R*(N+L+1)^6*4^L) hsum]
  have hRN : N+L+1 ≤ R*(N+L+1)^6 := by nlinarith
  have hRR : R ≤ R*(N+L+1)^6 := by nlinarith
  nlinarith

theorem cachedTotal_envelope {N : ℕ} (hN : 2≤N) {B beta u : ℝ}
    (hB : 0<B) (hBT : B<betaThreshold 2) (hu : 0<u) (hu1 : u<1)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    ((cachedTotal N B u χ (prepareInput 2 beta J)).operations : ℝ) ≤
      (81*amplitude B+4096*colorAmplitude B)*((N:ℝ)+1)^11*Real.exp (growth B*budget B u) := by
  have hNp : (1:ℝ) ≤ (N:ℝ)+1 := by have := (Nat.cast_nonneg N : (0:ℝ)≤N); linarith
  have hA := amplitude_pos hB hBT
  have hCA : 0<colorAmplitude B := by have := sizeFactor_pos hB hBT; unfold colorAmplitude; positivity
  by_cases he : exactBranch N B u
  · have hentries : (prepareInput 2 beta J).entries.length ≤
        ((univ : Finset (Fin N)).powersetCard 2).card := by simp [prepareInput]
    have hc := HigherOrderControl.localControl_le (prepareInput 2 beta J)
      ((univ : Finset (Fin N)).powersetCard 2) univ hentries
    have hchoose : N.choose 2+1 ≤ 2*(N+1)^2 := by
      have h := (Nat.choose_le_pow N 2).trans (Nat.pow_le_pow_left (by omega : N≤N+1) 2)
      have h1 : 1≤(N+1)^2 := Nat.one_le_pow _ _ (by omega)
      omega
    have hfactor : HigherOrderControl.localFactor N (N.choose 2) ≤ 80*(N+1)^6 := by
      unfold HigherOrderControl.localFactor
      calc
        _ ≤ 20*(N+1)^2*(2*(N+1)^2)^2 := by gcongr
        _ = _ := by ring
    simp only [Fintype.card_fin,card_powersetCard,card_univ] at hc
    have hc' := hc.trans (Nat.mul_le_mul_right _ hfactor)
    have h1 : 1≤(N+1)^6 := Nat.one_le_pow _ _ (by omega)
    have hfull : (cachedTotal N B u χ (prepareInput 2 beta J)).operations ≤
        81*(N+1)^6*(exactEvaluator 2 (preparedWeight (prepareInput 2 beta J))).operations := by
      simp only [cachedTotal,if_pos he]
      simp only [exactEvaluator]
      nlinarith [Nat.mul_le_mul_right (localEvaluator (univ.powersetCard 2)
        (preparedWeight (prepareInput 2 beta J)) univ).operations h1]
    have hcR : ((cachedTotal N B u χ (prepareInput 2 beta J)).operations : ℝ) ≤
        81*((N:ℝ)+1)^6*((exactEvaluator 2 (preparedWeight (prepareInput 2 beta J))).operations : ℝ) := by
      exact_mod_cast hfull
    have har : ((exactEvaluator 2 (preparedWeight (prepareInput 2 beta J))).operations : ℝ) ≤
        8*((N:ℝ)+1)^2*(2:ℝ)^N := by
      exact_mod_cast (by simpa only [Fintype.card_fin] using
        exactEvaluator_cost (V := Fin N) (p := 2) (by omega) (preparedWeight (prepareInput 2 beta J)))
    have hex := exact_envelope hN hB hBT hu hu1 he
    calc
      _ ≤ 81*((N:ℝ)+1)^6*(amplitude B*((N:ℝ)+1)^5*Real.exp (growth B*budget B u)) :=
        hcR.trans (mul_le_mul_of_nonneg_left (har.trans hex) (by positivity))
      _ = (81*amplitude B)*((N:ℝ)+1)^11*Real.exp (growth B*budget B u) := by ring
      _ ≤ _ := by gcongr; linarith
  · have hs := selectedSize_spec hB hBT hu hu1 he
    have hm : selectedSize N B u-1+1=selectedSize N B u := by omega
    have hcost := SKCountedExecution.generatedEstimator_operations_le
      (selectedSize N B u-1) (edgeLimit B u) (repetitions B u) (repetitions_pos B u)
      χ (preparedWeight (prepareInput 2 beta J))
    simp only [Fintype.card_fin,hm] at hcost
    have ho := approximate_overhead (N := N) (L := edgeLimit B u) (repetitions_pos B u) hs.1
    have hfull : (cachedTotal N B u χ (prepareInput 2 beta J)).operations ≤
        4096*repetitions B u*(N+edgeLimit B u+1)^6*4^(edgeLimit B u)*
          (∑b∈range (selectedSize N B u),N.choose b*36^b) := by
      simp only [cachedTotal,if_neg he]
      nlinarith
    have hfullR : ((cachedTotal N B u χ (prepareInput 2 beta J)).operations : ℝ) ≤
        4096*((repetitions B u:ℝ)*((N:ℝ)+edgeLimit B u+1)^6*4^(edgeLimit B u)*
          (∑b∈range (selectedSize N B u),(N.choose b:ℝ)*36^b)) := by
      exact_mod_cast (by simpa only [Nat.mul_assoc] using hfull)
    have hex := approximate_envelope_power 6 hN hB hBT hu hu1 he
    have hpow : ((N:ℝ)+1)^7 ≤ ((N:ℝ)+1)^11 := pow_le_pow_right₀ hNp (by omega)
    calc
      _ ≤ 4096*(colorAmplitude B*((N:ℝ)+1)^7*Real.exp (growth B*budget B u)) :=
        hfullR.trans (mul_le_mul_of_nonneg_left hex (by norm_num))
      _ ≤ (81*amplitude B+4096*colorAmplitude B)*((N:ℝ)+1)^11*Real.exp (growth B*budget B u) := by
        nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0≤4096*colorAmplitude B*Real.exp (growth B*budget B u)),
          mul_nonneg (by positivity : 0≤81*amplitude B) (by positivity : 0≤((N:ℝ)+1)^11*Real.exp (growth B*budget B u))]

/-- Includes input generation, floor initialization, cutoff scan and branch
control in addition to the counted evaluator. -/
def execute (N : ℕ) (B beta u : ℝ) (χ : Randomness N B u)
    (J : Finset (Fin N) → ℝ) : Computation :=
  let input := prepareInput 2 beta J
  let r := cachedTotal N B u χ input
  ⟨r.value, input.operations+5+6*scanEvaluations N B u+
    HigherOrderControl.setupControl 2 N+r.operations⟩

theorem execute_operations (N : ℕ) (B beta u : ℝ)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    (execute N B beta u χ J).operations = (prepareInput 2 beta J).operations+5+
      6*scanEvaluations N B u+HigherOrderControl.setupControl 2 N+
      (cachedTotal N B u χ (prepareInput 2 beta J)).operations := rfl

theorem execute_value {N : ℕ} {B beta u : ℝ}
    (hB : 0<B) (hBT : B<betaThreshold 2) (hu : 0<u) (hu1 : u<1)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    (execute N B beta u χ J).value=fastRun N B beta u χ J := by
  exact (cachedTotal_value _ _ _ _ _).trans (cachedEvaluator_value hB hBT hu hu1 χ J)

theorem execution_envelope {N : ℕ} (hN : 2≤N) {B beta u : ℝ}
    (hB : 0<B) (hBT : B<betaThreshold 2) (hu : 0<u) (hu1 : u<1)
    (χ : Randomness N B u) (J : Finset (Fin N) → ℝ) :
    ((execute N B beta u χ J).operations : ℝ) ≤
      totalAmplitude B*((N:ℝ)+1)^11*Real.exp (growth B*budget B u) := by
  have h := valid hB hBT
  have hLam := logBudget_pos h.budget_ge hu hu1
  have hexp : 1≤Real.exp (growth B*budget B u) := Real.one_le_exp_iff.mpr (mul_pos (growth_pos hB hBT) hLam).le
  have hNp : (1:ℝ)≤(N:ℝ)+1 := by have := (Nat.cast_nonneg N : (0:ℝ)≤N); linarith
  have hP : 1≤((N:ℝ)+1)^11 := one_le_pow₀ hNp
  have hNpow : (N:ℝ)≤((N:ℝ)+1)^11 := (by linarith : (N:ℝ)≤(N:ℝ)+1).trans (le_self_pow₀ hNp (by omega))
  have hpow : ((N:ℝ)+1)^2≤((N:ℝ)+1)^11 := pow_le_pow_right₀ hNp (by omega)
  have hpow6 : ((N:ℝ)+1)^6≤((N:ℝ)+1)^11 := pow_le_pow_right₀ hNp (by omega)
  have hprep : ((prepareInput 2 beta J).operations:ℝ)≤16*((N:ℝ)+1)^2 := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using prepareInput_cost (V:=Fin N) (by omega : 0<2) beta J)
  have hscan : (scanEvaluations N B u:ℝ)≤N := by exact_mod_cast scanEvaluations_le (N:=N) (u:=u) hB hBT
  have hchoose : N.choose 2+1≤2*(N+1)^2 := by
    have h := (Nat.choose_le_pow N 2).trans (Nat.pow_le_pow_left (by omega : N≤N+1) 2)
    have h1 : 1≤(N+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hsetup : (HigherOrderControl.setupControl 2 N:ℝ)≤400*((N:ℝ)+1)^6 := by
    have hS := HigherOrderControl.setupControl_le hN
    have hbound : HigherOrderControl.setupControl 2 N≤400*(N+1)^6 := by
      calc
        _ ≤ 100*(N+1)^2*(N.choose 2+1)^2 := hS
        _ ≤ 100*(N+1)^2*(2*(N+1)^2)^2 := by gcongr
        _ = _ := by ring
    exact_mod_cast hbound
  have hbase := cachedTotal_envelope (beta := beta) hN hB hBT hu hu1 χ J
  have hinit : ((prepareInput 2 beta J).operations:ℝ)+5+6*scanEvaluations N B u+
      HigherOrderControl.setupControl 2 N≤1000*((N:ℝ)+1)^11 := by nlinarith
  simp only [execute]
  push_cast
  unfold totalAmplitude
  nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : 0≤1000*((N:ℝ)+1)^11)]

theorem execution_polynomial {B : ℝ} (hB : 0<B) (hBT : B<betaThreshold 2) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2≤N → ∀ beta u : ℝ, 0<u → u<1 →
      ∀ (χ : Randomness N B u) (J : Finset (Fin N) → ℝ),
        ((execute N B beta u χ J).operations:ℝ)≤C*(N:ℝ)^C*u^(-C) := by
  let C := envelopeConstant (totalAmplitude B) (budgetConstant B) (growth B) 11
  refine ⟨C,envelopeConstant_pos _ _ _ _,?_⟩
  intro N hN beta u hu hu1 χ J
  have h := valid hB hBT
  exact (execution_envelope hN hB hBT hu hu1 χ J).trans
    (envelope_le_polynomial (totalAmplitude_pos hB hBT).le (by linarith [h.budget_ge]) (by omega) hu hu1.le)

end SpinGlass.SKTotalCost
