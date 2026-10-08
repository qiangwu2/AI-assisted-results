import SpinGlass.SupportMassTail
import SpinGlass.DisorderUniform

/-!
# The support approximation under the original disorder law

This file connects the actual normalized partition function to the retained
support polynomial and proves Proposition 5.3 for iid symmetric variance-one
real couplings. No mean-square estimate is an assumption.
-/

noncomputable section
namespace SpinGlass.SupportMeanSquare
open Finset Real MeasureTheory
open SpinGlass.Expansion SpinGlass.SupportMassCounting SpinGlass.SupportMassBound
open SpinGlass.SupportMassTail SpinGlass.Disorder SpinGlass.UniformMass SpinGlass.UniformMassEntropy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The retained support polynomial, evaluated at the actual tanh coupling weights. -/
def supportApproximation (p cutoff : ℕ) (a : ℝ) (J : Finset V → ℝ) : ℝ :=
  ∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs p : Finset (Finset (Finset V))).filter
    (fun Γ => (SpinGlass.Hypergraph.support Γ).card ≤ cutoff),
    monomial (fun _ => a) Γ J

/-- Orthogonality identifies the actual approximation error with the omitted support mass. -/
theorem support_error_eq_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (p cutoff : ℕ) (a : ℝ) :
    (∫ J : Finset V → ℝ,
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard p)
          (fun e => a * J e) - supportApproximation p cutoff a J)^2 ∂iidLaw μ) =
      supportTail (V := V) p cutoff (secondMoment μ a) := by
  have hfull (J : Finset V → ℝ) :
      SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset V).powersetCard p)
          (fun e => a * J e) =
      ∑ Γ ∈ (SpinGlass.SupportMassCounting.evenGraphs p : Finset (Finset (Finset V))),
        monomial (fun _ => a) Γ J := by
    rw [SpinGlass.Partition.normalizedPartition_eq_even_sum]
    rfl
  simp_rw [hfull]
  have h := retained_polynomial_error μ hμ (fun _ : Finset V => a)
    (SpinGlass.SupportMassCounting.evenGraphs p) (fun _ => 1)
    (fun Γ => (SpinGlass.Hypergraph.support Γ).card ≤ cutoff)
  simpa only [supportApproximation, supportTail, one_mul, one_pow, Finset.prod_const, not_le] using h

/-- The physical p-spin scaling gives the exact uniform second-moment coefficient bound. -/
theorem pure_secondMoment_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) {N p : ℕ} (hN : 0 < N)
    {β B : ℝ} (hβ : 0 ≤ β) (hβB : β ≤ B) (hB : 0 ≤ B) :
    secondMoment μ (pureScale N p β) ≤ B^2/(N : ℝ)^(p-1) := by
  calc
    _ ≤ pureScale N p β ^ 2 := secondMoment_le_scale_sq μ hunit _
    _ = β^2/(N : ℝ)^(p-1) := pureScale_sq hN β
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- Proposition 5.3 for the actual normalized partition function, including
arbitrary symmetric variance-one couplings and every `β` in `[0,B]`. -/
theorem pure_support_mean_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N p cutoff : ℕ} (hp : 3 ≤ p) (hpN : p ≤ N)
    {β B βplus alpha : ℝ} (hβ : 0 ≤ β) (hβB : β ≤ B) (hB : 0 < B)
    (hBplus : B < βplus) (hplusT : βplus^2 < thresholdSquared p)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hsmall : aZero p B * alpha^(p-1) ≤ 1)
    (hgap : 2 ≤ kappa p * (Real.log (1/(supportScale p B*alpha))-1))
    (hcut : cutoff < Nat.floor (alpha*N)) :
    (∫ J : Finset (Fin N) → ℝ,
      (SpinGlass.Partition.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard p)
          (fun e => pureScale N p β * J e) -
        supportApproximation p cutoff (pureScale N p β) J)^2 ∂iidLaw μ) ≤
      2 * Real.exp (-SpinGlass.CutoffTail.phi (kappa p) (supportScale p B) N (cutoff+1)) +
      massConstant p (βplus^2) *
        Real.exp (-(2*alpha/(p : ℝ)*Real.log (1/(B/βplus)^2))*(N : ℝ)) := by
  rw [support_error_eq_tail μ hμ]
  have hN : 0 < N := by omega
  have hplus : 0 < βplus := hB.trans hBplus
  have hratio : 0 < B/βplus := div_pos hB hplus
  have hratio1 : B/βplus ≤ 1 := (div_le_one hplus).mpr hBplus.le
  have hr := secondMoment_nonneg μ (pureScale N p β)
  have hrB := pure_secondMoment_bound μ hunit (p := p) hN hβ hβB hB.le
  have hrq : secondMoment μ (pureScale N p β) ≤
      (B/βplus)^2 * (βplus^2/(N : ℝ)^(p-1)) := by
    have heq : (B/βplus)^2 * (βplus^2/(N : ℝ)^(p-1)) = B^2/(N : ℝ)^(p-1) := by
      field_simp
    rw [heq]
    exact hrB
  exact support_truncation_tail (V := Fin N) (Fintype.card_fin N) hp hpN hB hr hrB
    (sq_nonneg βplus) hplusT (sq_pos_of_pos hratio) (pow_le_one₀ hratio.le hratio1) hrq
    halpha halpha1 hsmall hgap hcut

end SpinGlass.SupportMeanSquare
