import SpinGlass.SKBranchingMass
import SpinGlass.UniformMass
import SpinGlass.CutoffTail
import SpinGlass.SKBranchingScalar

/-! Actual SK branching tails, their finite split, and the large-branch remainder. -/
noncomputable section
namespace SpinGlass.SKBranching
open scoped BigOperators
open Finset Real SpinGlass.Expansion
open SpinGlass.UniformMassEntropy SpinGlass.UniformMass
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Total squared mass at a fixed actual branching cardinality. -/
def branchMass (b : ℕ) (r : ℝ) : ℝ :=
  ∑ Γ ∈ branchCardFamily (V := V) b, r ^ Γ.card

/-- Total squared mass omitted by the actual branching cutoff. -/
def branchTail (D : ℕ) (r : ℝ) : ℝ :=
  ∑ Γ ∈ (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
    (fun Γ => D < (SpinGlass.Hypergraph.branch Γ).card), r ^ Γ.card

/-- Exact split of the actual branching tail into the finite small range and remainder. -/
theorem branchTail_split (D K : ℕ) (hDK : D ≤ K) (r : ℝ) :
    branchTail (V := V) D r =
      (∑ b ∈ Finset.Ico (D + 1) (K + 1), branchMass (V := V) b r) +
        branchTail (V := V) K r := by
  have hf := Finset.sum_fiberwise_eq_sum_filter
    (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id))
    (Finset.Ico (D + 1) (K + 1)) (fun Γ => (SpinGlass.Hypergraph.branch Γ).card)
    (fun Γ => r ^ Γ.card)
  change (∑ b ∈ Finset.Ico (D + 1) (K + 1), branchMass (V := V) b r) = _ at hf
  rw [hf]
  unfold branchTail
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  simp only [Finset.mem_Ico]
  by_cases hD : D < (SpinGlass.Hypergraph.branch Γ).card
  · by_cases hK : K < (SpinGlass.Hypergraph.branch Γ).card
    · have hn : ¬(D + 1 ≤ (SpinGlass.Hypergraph.branch Γ).card ∧
          (SpinGlass.Hypergraph.branch Γ).card < K + 1) := by omega
      simp [hD, hK, hn]
    · have hh : D + 1 ≤ (SpinGlass.Hypergraph.branch Γ).card ∧
          (SpinGlass.Hypergraph.branch Γ).card < K + 1 := by omega
      simp [hD, hK, hh]
  · have hK : ¬ K < (SpinGlass.Hypergraph.branch Γ).card := by omega
    have hn : ¬(D + 1 ≤ (SpinGlass.Hypergraph.branch Γ).card ∧
          (SpinGlass.Hypergraph.branch Γ).card < K + 1) := by omega
    simp [hD, hK, hn]

/-- Many branching vertices force many actual edges, so the proved inflated mass
bound controls the full large-branch tail with the exact manuscript exponent. -/
theorem large_branch_tail {N : ℕ} (hcard : Fintype.card V = N) (hN : 2 ≤ N)
    {vplus r q alpha : ℝ} (hvplus : 0 ≤ vplus) (hvT : vplus < thresholdSquared 2)
    (hr : 0 ≤ r) (hq : 0 < q) (hq1 : q ≤ 1) (halpha : 0 ≤ alpha)
    (hrq : r ≤ q * (vplus / (N : ℝ))) :
    branchTail (V := V) (Nat.floor (alpha * N)) r ≤
      massConstant 2 vplus * Real.exp (-(2 * alpha * Real.log (1 / q)) * (N : ℝ)) := by
  have hαN : 0 ≤ alpha * (N : ℝ) := mul_nonneg halpha (Nat.cast_nonneg _)
  have hsub : (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
      (fun Γ => Nat.floor (alpha * N) < (SpinGlass.Hypergraph.branch Γ).card) ⊆
      (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
        (fun Γ => 2 * alpha * (N : ℝ) < (Γ.card : ℝ)) := by
    intro Γ hΓ
    obtain ⟨hG, hb⟩ := Finset.mem_filter.mp hΓ
    have hbranch : alpha * (N : ℝ) < (SpinGlass.Hypergraph.branch Γ).card :=
      (Nat.floor_lt hαN).mp hb
    have hsimple : ∀ e ∈ Γ, e.card = 2 := by
      intro e he
      exact (Finset.mem_powersetCard.mp
        ((Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1) he)).2
    have hd := SpinGlass.Hypergraph.sk_twice_branch_le_edges Γ hsimple
    have hdR : (2 : ℝ) * (SpinGlass.Hypergraph.branch Γ).card ≤ Γ.card := by exact_mod_cast hd
    exact Finset.mem_filter.mpr ⟨hG, by nlinarith⟩
  have hc := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun Γ _ _ => pow_nonneg hr Γ.card)
  have hNV : 2 ≤ Fintype.card V := by omega
  have hrqV : r ≤ q * (vplus / (Fintype.card V : ℝ) ^ (2 - 1)) := by
    simpa only [hcard, Nat.reduceSub, pow_one] using hrq
  have he := graphical_edge_tail_real (V := V) (by omega : 0 < 2) hNV
    hvplus hvT hr hq hq1 (by positivity : 0 ≤ 2 * alpha * (N : ℝ)) hrqV
  have h := hc.trans (he.1.trans he.2)
  change branchTail (V := V) (Nat.floor (alpha * N)) r ≤ _ at h
  convert h using 1
  rw [Real.rpow_def_of_pos hq, one_div, Real.log_inv]
  congr 2
  ring


/-- Lemma 6.1 with the actual finite graph mass and the paper's exact constants. -/
theorem branchMass_bound {N b : ℕ} (hcard : Fintype.card V = N)
    (hN : 0 < N) (hb : 0 < b) {B r : ℝ} (hB : 0 ≤ B) (hB1 : B < 1)
    (hr : 0 ≤ r) (hrB : r ≤ B ^ 2 / (N : ℝ)) :
    branchMass (V := V) b r ≤
      SpinGlass.SKBranchingScalar.massConstant B *
        (SpinGlass.SKBranchingScalar.branchConstant B * b / N) ^ b := by
  have hNr : (Fintype.card V : ℝ) * r < 1 := by
    rw [hcard]
    have h := (le_div_iff₀ (Nat.cast_pos.mpr hN : (0 : ℝ) < N)).mp hrB
    nlinarith
  have h := branchCard_mass_pairing_bound (V := V) b hr hNr
  rw [hcard] at h
  exact h.trans (SpinGlass.SKBranchingScalar.gaussian_bound_to_branch_bound hN hb hB hB1 hr hrB)

/-- The nonbranching mass, including arbitrarily long cycles, has the exact C_B bound. -/
theorem branchMass_zero_bound {N : ℕ} (hcard : Fintype.card V = N)
    (hN : 0 < N) {B r : ℝ} (hB : 0 ≤ B) (hB1 : B < 1)
    (hr : 0 ≤ r) (hrB : r ≤ B ^ 2 / (N : ℝ)) :
    branchMass (V := V) 0 r ≤ SpinGlass.SKBranchingScalar.massConstant B := by
  have hNr : (Fintype.card V : ℝ) * r < 1 := by
    rw [hcard]
    have h := (le_div_iff₀ (Nat.cast_pos.mpr hN : (0 : ℝ) < N)).mp hrB
    nlinarith
  have h := branchCard_mass_pairing_bound (V := V) 0 hr hNr
  rw [hcard] at h
  exact h.trans (SpinGlass.SKBranchingScalar.zero_branch_bound hN hB hB1 hr hrB)

/-- The exponential version of the verified growing-branch-count estimate. -/
theorem branchMass_bound_exp {N b : ℕ} (hcard : Fintype.card V = N)
    (hN : 0 < N) (hb : 0 < b) {B r : ℝ} (hB : 0 ≤ B) (hB1 : B < 1)
    (hr : 0 ≤ r) (hrB : r ≤ B ^ 2 / (N : ℝ)) :
    branchMass (V := V) b r ≤
      SpinGlass.SKBranchingScalar.massConstant B *
        Real.exp (-SpinGlass.CutoffTail.phi 1
          (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N b) := by
  apply (branchMass_bound hcard hN hb hB hB1 hr hrB).trans
  exact mul_le_mul_of_nonneg_left (SpinGlass.SKBranchingScalar.branch_power_le_exp hN hb B)
    (zero_le_one.trans (SpinGlass.SKBranchingScalar.massConstant_ge_one hB hB1))

/-- The full branching tail estimate with its exact finite and extensive terms. -/
theorem branch_truncation_tail {N D : ℕ} (hcard : Fintype.card V = N) (hN : 2 ≤ N)
    {B r vplus q alpha : ℝ} (hB : 0 ≤ B) (hB1 : B < 1)
    (hr : 0 ≤ r) (hrB : r ≤ B ^ 2 / (N : ℝ))
    (hvplus : 0 ≤ vplus) (hvT : vplus < thresholdSquared 2)
    (hq : 0 < q) (hq1 : q ≤ 1) (hrq : r ≤ q * (vplus / (N : ℝ)))
    (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (max 1 (SpinGlass.SKBranchingScalar.branchConstant B) * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * N)) :
    branchTail (V := V) D r ≤
      2 * SpinGlass.SKBranchingScalar.massConstant B *
        Real.exp (-SpinGlass.CutoffTail.phi 1
          (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N (D + 1)) +
      massConstant 2 vplus * Real.exp (-(2 * alpha * Real.log (1 / q)) * (N : ℝ)) := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hfloor : (Nat.floor (alpha * N) : ℝ) ≤ alpha * N := Nat.floor_le (by positivity)
  have hsmall : (∑ b ∈ Finset.Ico (D + 1) (Nat.floor (alpha * N) + 1), branchMass (V := V) b r) ≤
      2 * SpinGlass.SKBranchingScalar.massConstant B *
        Real.exp (-SpinGlass.CutoffTail.phi 1
          (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N (D + 1)) := by
    calc
      _ ≤ ∑ b ∈ Finset.Ico (D + 1) (Nat.floor (alpha * N) + 1),
          SpinGlass.SKBranchingScalar.massConstant B *
            Real.exp (-SpinGlass.CutoffTail.phi 1
              (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N b) := by
        apply Finset.sum_le_sum
        intro b hb
        have hbpos : 0 < b := by have := (Finset.mem_Ico.mp hb).1; omega
        exact branchMass_bound_exp hcard hNpos hbpos hB hB1 hr hrB
      _ = SpinGlass.SKBranchingScalar.massConstant B *
          (∑ b ∈ Finset.Ico (D + 1) (Nat.floor (alpha * N) + 1),
            Real.exp (-SpinGlass.CutoffTail.phi 1
              (max 1 (SpinGlass.SKBranchingScalar.branchConstant B)) N b)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := by
        have h := SpinGlass.CutoffTail.phi_tail (by norm_num : (0 : ℝ) ≤ 1)
          (zero_lt_one.trans_le (le_max_left 1 (SpinGlass.SKBranchingScalar.branchConstant B)))
          hNR halpha (by simpa using hgap) (m := D + 1) (by omega) hfloor
        have hc := mul_le_mul_of_nonneg_left h
          (zero_le_one.trans (SpinGlass.SKBranchingScalar.massConstant_ge_one hB hB1))
        simpa only [Nat.cast_add, Nat.cast_one, ← mul_assoc, mul_comm _ (2 : ℝ)] using hc
  rw [branchTail_split D (Nat.floor (alpha * N)) hcut.le r]
  exact add_le_add hsmall (large_branch_tail hcard hN hvplus hvT hr hq hq1 halpha.le hrq)

end SpinGlass.SKBranching
