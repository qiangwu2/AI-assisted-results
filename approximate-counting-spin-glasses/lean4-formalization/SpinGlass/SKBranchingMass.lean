import SpinGlass.SKBranchingMassFinite
import SpinGlass.Expansion

/-! Actual finite SK branching families and their Gaussian pairing bound. -/
noncomputable section
namespace SpinGlass.SKBranching
open scoped BigOperators Nat
open MeasureTheory Finset Real
open SpinGlass.Expansion
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite choices of permitted degrees at a given branching set. -/
def degreeChoices (A : Finset V) (K : ℕ) (v : V) : Finset ℕ :=
  if v ∈ A then (Finset.range K).image (fun j => 2 * j + 4) else {0, 2}

/-- All permitted degrees are even. -/
theorem degreeChoices_even (A : Finset V) (K : ℕ) (v : V) {d : ℕ}
    (hd : d ∈ degreeChoices A K v) : Even d := by
  unfold degreeChoices at hd
  split_ifs at hd with h
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨j + 2, by omega⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> decide

/-- The complete finite grid consists only of even-total degree sequences. -/
theorem degreeGrid_even (A : Finset V) (K : ℕ) (d : V → ℕ)
    (hd : d ∈ Fintype.piFinset (degreeChoices A K)) : ∃ k, ∑ v, d v = 2 * k := by
  refine ⟨∑ v, d v / 2, ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact (Nat.mul_div_cancel' ((even_iff_two_dvd).mp
    (degreeChoices_even A K v (Fintype.mem_piFinset.mp hd v)))).symm

/-- The finite product of degree-generating polynomials. -/
def degreePolynomial (A : Finset V) (K : ℕ) (r x : ℝ) : ℝ :=
  ∏ v, ∑ d ∈ degreeChoices A K v, (Real.sqrt r * x) ^ d / d.factorial

theorem degreePolynomial_eq_sum (A : Finset V) (K : ℕ) (r x : ℝ) :
    degreePolynomial A K r x =
      ∑ d ∈ Fintype.piFinset (degreeChoices A K), degreeMonomial r d x := by
  exact Finset.prod_univ_sum _ _

theorem degreePolynomial_nonneg (A : Finset V) (K : ℕ) (r x : ℝ) :
    0 ≤ degreePolynomial A K r x := by
  apply Finset.prod_nonneg
  intro v hv
  apply Finset.sum_nonneg
  intro d hd
  exact div_nonneg ((degreeChoices_even A K v hd).pow_nonneg _) (Nat.cast_nonneg _)

/-- The actual finite even-degree simple graph family with exact branching set A. -/
def branchFamily (A : Finset V) : Finset (Finset (Finset V)) :=
  (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
    (fun Γ => SpinGlass.Hypergraph.branch Γ = A)

theorem branchFamily_simple (A : Finset V) {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ branchFamily A) : ∀ e ∈ Γ, e.card = 2 := by
  have hs := (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hΓ).1).1)
  intro e he
  exact (Finset.mem_powersetCard.mp (hs he)).2

omit [Fintype V] in
theorem mem_branch_iff_degree (Γ : Finset (Finset V)) (v : V) :
    v ∈ SpinGlass.Hypergraph.branch Γ ↔ 4 ≤ SpinGlass.Hypergraph.degree Γ v := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have hpos : 0 < (Γ.filter (fun e => v ∈ e)).card := by
      change 0 < SpinGlass.Hypergraph.degree Γ v
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    exact Finset.mem_filter.mpr ⟨SpinGlass.Hypergraph.mem_support_iff.mpr
      ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩, h⟩

/-- The finite degree box really contains every graph under consideration. -/
theorem branchFamily_degree_cover (A : Finset V) {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ branchFamily A) :
    SpinGlass.Hypergraph.degree Γ ∈
      Fintype.piFinset (degreeChoices A (Fintype.card (Finset V) + 1)) := by
  apply Fintype.mem_piFinset.mpr
  intro v
  have heven : Even (SpinGlass.Hypergraph.degree Γ v) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hΓ).1).2 v
  have hmod := Nat.even_iff.mp heven
  have hbranch : SpinGlass.Hypergraph.branch Γ = A := (Finset.mem_filter.mp hΓ).2
  have hdeg : SpinGlass.Hypergraph.degree Γ v ≤ Fintype.card (Finset V) :=
    (Finset.card_filter_le _ _).trans (Finset.card_le_univ Γ)
  unfold degreeChoices
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    have hfour : 4 ≤ SpinGlass.Hypergraph.degree Γ v :=
      (mem_branch_iff_degree Γ v).mp (hbranch.symm ▸ hv)
    apply Finset.mem_image.mpr
    refine ⟨SpinGlass.Hypergraph.degree Γ v / 2 - 2, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · rw [if_neg hv]
    have hfour : ¬4 ≤ SpinGlass.Hypergraph.degree Γ v := by
      intro h
      exact hv (hbranch ▸ (mem_branch_iff_degree Γ v).mpr h)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- First inequality of the Gaussian pairing argument for the actual graph family. -/
theorem branchFamily_mass_le_degreePolynomial (A : Finset V) (r : ℝ) (hr : 0 ≤ r) :
    (∑ Γ ∈ branchFamily A, r ^ Γ.card) ≤
      gaussianMean (degreePolynomial A (Fintype.card (Finset V) + 1) r) := by
  have h := finite_degree_mass_le_gaussian (branchFamily A)
    (fun Γ hΓ => branchFamily_simple A hΓ) r hr
    (Fintype.piFinset (degreeChoices A (Fintype.card (Finset V) + 1)))
    (fun Γ hΓ => branchFamily_degree_cover A hΓ)
    (degreeGrid_even A (Fintype.card (Finset V) + 1))
  simpa only [← degreePolynomial_eq_sum] using h

/-- The finite degree polynomial has the exact pointwise exponential majorant. -/
theorem degreePolynomial_le (A : Finset V) (K : ℕ) (r x : ℝ) :
    degreePolynomial A K r x ≤
      (((Real.sqrt r * x) ^ 4 / 24) ^ A.card) *
        Real.exp ((Fintype.card V : ℝ) * (Real.sqrt r * x) ^ 2 / 2) := by
  let y := Real.sqrt r * x
  have hvertex (v : V) : (∑ d ∈ degreeChoices A K v, y ^ d / d.factorial) ≤
      (if v ∈ A then y ^ 4 / 24 else 1) * Real.exp (y ^ 2 / 2) := by
    by_cases hv : v ∈ A
    · simp only [degreeChoices, hv, if_true]
      rw [Finset.sum_image (fun j hj k hk h => by omega)]
      exact finite_branching_series_le y K
    · simp only [degreeChoices, hv, if_false]
      norm_num
      exact nonbranch_factor_le y
  apply (Finset.prod_le_prod (fun v hv => Finset.sum_nonneg fun d hd =>
    div_nonneg ((degreeChoices_even A K v hd).pow_nonneg y) (Nat.cast_nonneg _))
      (fun v hv => hvertex v)).trans_eq
  rw [Finset.prod_mul_distrib]
  have hprod : (∏ v : V, if v ∈ A then y ^ 4 / 24 else 1) = (y ^ 4 / 24) ^ A.card := by
    rw [Finset.prod_ite_mem_eq, Finset.prod_const]
  rw [hprod, Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  congr 2
  ring

theorem gaussianIntegrable_tilted_monomial (k : ℕ) {t : ℝ} (ht : t < 1) :
    GaussianIntegrable (fun x : ℝ => x ^ (2 * k) * Real.exp (t * x ^ 2 / 2)) := by
  unfold GaussianIntegrable
  convert integrable_even_gaussian k (b := (1 - t) / 2) (by linarith) using 1
  funext x
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

/-- Rewrite the pointwise majorant in the form of the exact tilted Gaussian moment. -/
theorem degree_majorant_eq (A : Finset V) (r : ℝ) (hr : 0 ≤ r) (x : ℝ) :
    (((Real.sqrt r * x) ^ 4 / 24) ^ A.card) *
      Real.exp ((Fintype.card V : ℝ) * (Real.sqrt r * x) ^ 2 / 2) =
      (r ^ (2 * A.card) / 24 ^ A.card) *
        (x ^ (4 * A.card) * Real.exp ((Fintype.card V : ℝ) * r * x ^ 2 / 2)) := by
  have hsqrt4 : Real.sqrt r ^ 4 = r ^ 2 := by
    calc _ = (Real.sqrt r ^ 2) ^ 2 := by ring
         _ = _ := by rw [Real.sq_sqrt hr]
  rw [mul_pow, hsqrt4, mul_pow, Real.sq_sqrt hr]
  rw [div_pow, mul_pow, ← pow_mul, ← pow_mul]
  rw [show (Fintype.card V : ℝ) * (r * x ^ 2) / 2 =
      (Fintype.card V : ℝ) * r * x ^ 2 / 2 by ring]
  ring

/-- The exact Gaussian pairing bound for each fixed actual branching set. -/
theorem branchFamily_mass_pairing_bound (A : Finset V) {r : ℝ}
    (hr : 0 ≤ r) (hNr : (Fintype.card V : ℝ) * r < 1) :
    (∑ Γ ∈ branchFamily A, r ^ Γ.card) ≤
      r ^ (2 * A.card) / 24 ^ A.card * ((4 * A.card - 1)‼ : ℝ) *
        (1 - (Fintype.card V : ℝ) * r) ^ (-((2 * A.card : ℕ) : ℝ) - 1 / 2) := by
  let K := Fintype.card (Finset V) + 1
  let c : ℝ := r ^ (2 * A.card) / 24 ^ A.card
  let g : ℝ → ℝ := fun x => c * (x ^ (4 * A.card) * Real.exp ((Fintype.card V : ℝ) * r * x ^ 2 / 2))
  have hg : GaussianIntegrable g := by
    have h := gaussianIntegrable_tilted_monomial (2 * A.card) hNr
    unfold GaussianIntegrable at h ⊢
    simpa only [g, mul_assoc, show 2 * (2 * A.card) = 4 * A.card by omega] using h.const_mul c
  have hpoint (x : ℝ) : degreePolynomial A K r x ≤ g x := by
    exact (degreePolynomial_le A K r x).trans_eq (degree_majorant_eq A r hr x)
  apply (branchFamily_mass_le_degreePolynomial A r hr).trans
  apply (gaussianMean_mono (degreePolynomial A K r) g
    (degreePolynomial_nonneg A K r) hg hpoint).trans_eq
  unfold g
  rw [gaussianMean_const_mul]
  have hmoment := gaussianMean_tilted_even_moment (2 * A.card) hNr
  simp only [show 2 * (2 * A.card) = 4 * A.card by omega] at hmoment
  rw [hmoment]
  dsimp [c]
  rw [show -(((2 * A.card : ℕ) : ℝ) + 1 / 2) =
      -((2 * A.card : ℕ) : ℝ) - 1 / 2 by ring]
  ring


/-- Actual even simple graphs with exactly b vertices of degree at least four. -/
def branchCardFamily (b : ℕ) : Finset (Finset (Finset V)) :=
  (((Finset.univ : Finset V).powersetCard 2).powerset.filter (IsEven id)).filter
    (fun Γ => (SpinGlass.Hypergraph.branch Γ).card = b)

/-- Partition the actual graph family by its exact branching set. -/
theorem branchCard_mass_eq (b : ℕ) (r : ℝ) :
    (∑ Γ ∈ branchCardFamily (V := V) b, r ^ Γ.card) =
      ∑ A ∈ (Finset.univ : Finset V).powersetCard b,
        ∑ Γ ∈ branchFamily A, r ^ Γ.card := by
  have hcover : ∀ Γ ∈ branchCardFamily (V := V) b,
      SpinGlass.Hypergraph.branch Γ ∈ (Finset.univ : Finset V).powersetCard b := by
    intro Γ hΓ
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hΓ).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hcover]
  apply Finset.sum_congr rfl
  intro A hA
  have hcard := (Finset.mem_powersetCard.mp hA).2
  congr 1
  ext Γ
  simp only [branchCardFamily, branchFamily, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2 ▸ hcard⟩, h.2⟩

/-- The exact finite-graph version of the SK pairing bound, before scalar estimates. -/
theorem branchCard_mass_pairing_bound (b : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hNr : (Fintype.card V : ℝ) * r < 1) :
    (∑ Γ ∈ branchCardFamily (V := V) b, r ^ Γ.card) ≤
      ((Fintype.card V).choose b : ℝ) *
        (r ^ (2 * b) / 24 ^ b * ((4 * b - 1)‼ : ℝ) *
          (1 - (Fintype.card V : ℝ) * r) ^ (-((2 * b : ℕ) : ℝ) - 1 / 2)) := by
  rw [branchCard_mass_eq]
  calc
    _ ≤ ∑ A ∈ (Finset.univ : Finset V).powersetCard b,
        r ^ (2 * b) / 24 ^ b * ((4 * b - 1)‼ : ℝ) *
          (1 - (Fintype.card V : ℝ) * r) ^ (-((2 * b : ℕ) : ℝ) - 1 / 2) := by
      apply Finset.sum_le_sum
      intro A hA
      simpa only [(Finset.mem_powersetCard.mp hA).2] using
        branchFamily_mass_pairing_bound A hr hNr
    _ = _ := by simp [Finset.card_powersetCard]

end SpinGlass.SKBranching
