import SpinGlass.SupportMassBound
import SpinGlass.CutoffTail

/-!
# The actual support-tail decomposition

Support tails are sums over omitted even hypergraphs. The large-support part
is controlled by the proved geometric edge tail and the proved degree bound.
-/

noncomputable section
namespace SpinGlass.SupportMassTail
open Finset Real
open SpinGlass.Expansion SpinGlass.SupportMassCounting SpinGlass.SupportMassBound
open SpinGlass.UniformMassEntropy SpinGlass.UniformMass

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The squared graphical mass omitted by the support cutoff. -/
def supportTail (p k : ℕ) (r : ℝ) : ℝ :=
  ∑ Γ ∈ (evenGraphs p : Finset (Finset (Finset V))).filter
    (fun Γ => k < (SpinGlass.Hypergraph.support Γ).card), r^Γ.card

/-- Exact decomposition into the finite small-support range and the large-support tail. -/
theorem supportTail_split (p k K : ℕ) (hkK : k ≤ K) (r : ℝ) :
    supportTail (V := V) p k r =
      (∑ v ∈ Finset.Ico (k+1) (K+1), supportMass (V := V) p v r) + supportTail (V := V) p K r := by
  have hf := Finset.sum_fiberwise_eq_sum_filter (evenGraphs p : Finset (Finset (Finset V)))
    (Finset.Ico (k+1) (K+1)) (fun Γ => (SpinGlass.Hypergraph.support Γ).card) (fun Γ => r^Γ.card)
  change (∑ v ∈ Finset.Ico (k+1) (K+1), supportMass (V := V) p v r) = _ at hf
  rw [hf]
  unfold supportTail
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  simp only [Finset.mem_Ico]
  by_cases hk : k < (SpinGlass.Hypergraph.support Γ).card
  · by_cases hK : K < (SpinGlass.Hypergraph.support Γ).card
    · have hnot : ¬(k+1 ≤ (SpinGlass.Hypergraph.support Γ).card ∧
          (SpinGlass.Hypergraph.support Γ).card < K+1) := by omega
      simp [hk, hK, hnot]
    · have hin : k+1 ≤ (SpinGlass.Hypergraph.support Γ).card ∧
          (SpinGlass.Hypergraph.support Γ).card < K+1 := by omega
      simp [hk, hK, hin]
  · have hK : ¬ K < (SpinGlass.Hypergraph.support Γ).card := by omega
    have hnot : ¬(k+1 ≤ (SpinGlass.Hypergraph.support Γ).card ∧
          (SpinGlass.Hypergraph.support Γ).card < K+1) := by omega
    simp [hk, hK, hnot]

/-- Rewriting the real geometric tail in the paper's exponential form. -/
theorem geometric_tail_eq_exp {q alpha : ℝ} (hq : 0 < q) (p N : ℕ) :
    q ^ ((2*alpha*(N : ℝ))/(p : ℝ)) =
      Real.exp (-(2*alpha/(p : ℝ)*Real.log (1/q))*(N : ℝ)) := by
  rw [Real.rpow_def_of_pos hq, one_div, Real.log_inv]
  congr 1
  ring

/-- The full large-support error term, with the exact constant and exponent. -/
theorem large_support_tail {N p : ℕ} (hcard : Fintype.card V = N)
    (hp : 0 < p) (hpN : p ≤ N) {vplus r q alpha : ℝ}
    (hvplus : 0 ≤ vplus) (hvT : vplus < thresholdSquared p)
    (hr : 0 ≤ r) (hq : 0 < q) (hq1 : q ≤ 1) (halpha : 0 ≤ alpha)
    (hrq : r ≤ q * (vplus/(N : ℝ)^(p-1))) :
    supportTail (V := V) p (Nat.floor (alpha*N)) r ≤
      massConstant p vplus * Real.exp (-(2*alpha/(p : ℝ)*Real.log (1/q))*(N : ℝ)) := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hN : 0 < N := lt_of_lt_of_le hp hpN
  have hαN : 0 ≤ alpha*(N : ℝ) := mul_nonneg halpha (Nat.cast_nonneg _)
  have ht : 0 ≤ (2*alpha*(N : ℝ))/(p : ℝ) := by positivity
  have hsub : (evenGraphs p : Finset (Finset (Finset V))).filter
      (fun Γ => Nat.floor (alpha*N) < (SpinGlass.Hypergraph.support Γ).card) ⊆
      (evenGraphs p).filter (fun Γ => (2*alpha*(N : ℝ))/(p : ℝ) < (Γ.card : ℝ)) := by
    intro Γ hΓ
    obtain ⟨hG, hsupp⟩ := Finset.mem_filter.mp hΓ
    have hsup : alpha*(N : ℝ) < (SpinGlass.Hypergraph.support Γ).card :=
      (Nat.floor_lt hαN).mp hsupp
    have hdegree := twice_support_le_edges hG
    have hdegreeR : (2:ℝ)*(SpinGlass.Hypergraph.support Γ).card ≤ (p : ℝ)*Γ.card := by
      exact_mod_cast hdegree
    refine Finset.mem_filter.mpr ⟨hG, ?_⟩
    apply (div_lt_iff₀ hpR).mpr
    nlinarith
  have hcompare := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun Γ _ _ => pow_nonneg hr Γ.card)
  have hpV : p ≤ Fintype.card V := by simpa only [hcard] using hpN
  have hrqV : r ≤ q*(vplus/(Fintype.card V : ℝ)^(p-1)) := by simpa only [hcard] using hrq
  have hedge := (graphical_edge_tail_real (V := V) hp hpV hvplus hvT hr hq hq1 ht hrqV).1.trans
    (graphical_edge_tail_real (V := V) hp hpV hvplus hvT hr hq hq1 ht hrqV).2
  have h := hcompare.trans hedge
  rw [geometric_tail_eq_exp hq p N] at h
  exact h

/-- The decay exponent of the large-support contribution is strictly positive. -/
theorem support_decay_pos {alpha q : ℝ} {p : ℕ} (halpha : 0 < alpha) (hp : 0 < p)
    (hq : 0 < q) (hq1 : q < 1) : 0 < 2*alpha/(p : ℝ)*Real.log (1/q) := by
  apply mul_pos (div_pos (mul_pos (by norm_num) halpha) (Nat.cast_pos.mpr hp))
  apply Real.log_pos
  exact (one_lt_div hq).mpr hq1

/-- The complete positive-mass version of Proposition 5.3. Both the small-support
geometric sum and the exponentially small large-support remainder are proved. -/
theorem support_truncation_tail {N p cutoff : ℕ} (hcard : Fintype.card V = N)
    (hp : 3 ≤ p) (hpN : p ≤ N) {B r vplus q alpha : ℝ}
    (hB : 0 < B) (hr : 0 ≤ r) (hrB : r ≤ B^2/(N : ℝ)^(p-1))
    (hvplus : 0 ≤ vplus) (hvT : vplus < thresholdSquared p)
    (hq : 0 < q) (hq1 : q ≤ 1) (hrq : r ≤ q*(vplus/(N : ℝ)^(p-1)))
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hsmall : aZero p B * alpha^(p-1) ≤ 1)
    (hgap : 2 ≤ kappa p * (Real.log (1/(supportScale p B*alpha))-1))
    (hcut : cutoff < Nat.floor (alpha*N)) :
    supportTail (V := V) p cutoff r ≤
      2 * Real.exp (-SpinGlass.CutoffTail.phi (kappa p) (supportScale p B) N (cutoff+1)) +
      massConstant p vplus * Real.exp (-(2*alpha/(p : ℝ)*Real.log (1/q))*(N : ℝ)) := by
  have hp0 : 0 < p := by omega
  have hN : 0 < N := lt_of_lt_of_le hp0 hpN
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hfloor : (Nat.floor (alpha*N) : ℝ) ≤ alpha*N := Nat.floor_le (by positivity)
  have hsmalltail : (∑ v ∈ Finset.Ico (cutoff+1) (Nat.floor (alpha*N)+1),
      supportMass (V := V) p v r) ≤
      2 * Real.exp (-SpinGlass.CutoffTail.phi (kappa p) (supportScale p B) N (cutoff+1)) := by
    calc
      _ ≤ ∑ v ∈ Finset.Ico (cutoff+1) (Nat.floor (alpha*N)+1),
          Real.exp (-SpinGlass.CutoffTail.phi (kappa p) (supportScale p B) N v) := by
        apply Finset.sum_le_sum
        intro v hv
        have hvi := Finset.mem_Ico.mp hv
        have hvpos : 0 < v := by omega
        have hvle : (v : ℝ) ≤ alpha*N := by
          have hvK : v ≤ Nat.floor (alpha*N) := by omega
          have hvKR : (v : ℝ) ≤ Nat.floor (alpha*N) := by exact_mod_cast hvK
          exact hvKR.trans hfloor
        have h := supportMass_bound_exp hcard hp hpN hvpos hB hr hrB halpha halpha1 hsmall hvle
        simpa only [SpinGlass.CutoffTail.phi, neg_mul] using h
      _ ≤ _ := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (SpinGlass.CutoffTail.phi_tail (kappa_pos hp).le (supportScale_pos p B)
            hNR halpha hgap (m := cutoff+1) (by omega) hfloor)
  have hlarge := large_support_tail hcard hp0 hpN hvplus hvT hr hq hq1 halpha.le hrq
  rw [supportTail_split p cutoff (Nat.floor (alpha*N)) hcut.le r]
  exact add_le_add hsmalltail hlarge

end SpinGlass.SupportMassTail
