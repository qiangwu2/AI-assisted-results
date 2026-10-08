import SpinGlass.HigherOrderTheorem
import SpinGlass.FiniteIndexCosts
import SpinGlass.RoundingExecution

/-! # Explicit non-arithmetic schedules for the support evaluator

This module records the bounded finite-index schedule as well as arithmetic.
Each edge filter is charged on every local spin assignment, even when it
rejects every edge. Prepared weights are charged for their actual list scans.
Set keys use finite bit vectors, so a key/subset comparison scans at most the
ambient number of coordinates. Full scans are charged conservatively.
-/
noncomputable section
namespace SpinGlass.HigherOrderControl
open scoped BigOperators
open Finset SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation
open SpinGlass.SupportEvaluation SpinGlass.HigherOrderAlgorithm SpinGlass.DesignConstants
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Metadata steps for one edge tested by a local spin product. Two full
vertex scans cover the subset and local-incidence tests; each cached lookup
visit compares one finite edge key. Spin-sign and iterator tests are included. -/
def edgeControl (input : PreparedInput V) (S e : Finset V) : ℕ :=
  2 + e.card * S.card + if e ⊆ S then
    2 * lookupVisits e input.entries * (Fintype.card V + 1)^2 +
      S.card * e.card + S.card + 4 else 0

/-- Concrete predicate/lookup comparisons used by the edge scan. -/
def edgeComparisons (input : PreparedInput V) (S e : Finset V) : ℕ :=
  (SpinGlass.FiniteIndexCosts.finsetSubset e S).comparisons +
    if e ⊆ S then (SpinGlass.FiniteIndexCosts.lookup e input.entries).2 else 0

theorem edgeComparisons_le (input : PreparedInput V) (S e : Finset V) :
    edgeComparisons input S e ≤ edgeControl input S e := by
  have hs := SpinGlass.FiniteIndexCosts.finsetSubset_comparisons e S
  have hl := SpinGlass.FiniteIndexCosts.lookup_comparisons_visits e input.entries
    (card_le_univ e) (fun x _ => card_le_univ x.1)
  have hn : (Fintype.card V)^2 ≤ (Fintype.card V+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul_right (2*lookupVisits e input.entries) hn
  unfold edgeComparisons edgeControl
  split_ifs <;> nlinarith

/-- The edge filter traverses all input edges for each spin assignment. -/
def spinControl (input : PreparedInput V) (edges : Finset (Finset V)) (S : Finset V) : ℕ :=
  1 + ∑ e ∈ edges, edgeControl input S e

/-- Full local schedule: normalization loop, finite Boolean-cube generation,
then a fresh edge scan for every local spin assignment. -/
def localControl (input : PreparedInput V) (edges : Finset (Finset V)) (S : Finset V) : ℕ :=
  S.card + 1 + 4 * (S.card + 1) * (2^S.card + 1) +
    ∑ _σ : S → Bool, (spinControl input edges S + 2)

def localFactor (N M : ℕ) : ℕ := 20 * (N+1)^2 * (M+1)^2

theorem edgeControl_le (input : PreparedInput V) (S e : Finset V) :
    edgeControl input S e ≤ (2 * input.entries.length + 8) * (Fintype.card V + 1)^2 := by
  have he := card_le_univ e
  have hs := card_le_univ S
  have hl := lookupVisits_le e input.entries
  have hm : e.card * S.card ≤ (Fintype.card V)^2 := by nlinarith
  have hp : 1 ≤ (Fintype.card V+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hn : Fintype.card V ≤ (Fintype.card V+1)^2 := by nlinarith
  have hlookup := Nat.mul_le_mul_right (2*((Fintype.card V+1)^2)) hl
  unfold edgeControl
  split_ifs <;> nlinarith

theorem spinControl_le (input : PreparedInput V) (edges : Finset (Finset V)) (S : Finset V)
    (hentries : input.entries.length ≤ edges.card) :
    spinControl input edges S ≤ 1 + edges.card * (2*edges.card+8) * (Fintype.card V+1)^2 := by
  unfold spinControl
  have hs : (∑ e ∈ edges, edgeControl input S e) ≤
      ∑ _e ∈ edges, (2*edges.card+8)*(Fintype.card V+1)^2 := by
    apply sum_le_sum
    intro e he
    exact (edgeControl_le input S e).trans (Nat.mul_le_mul_right _ (by omega))
  simp only [sum_const, smul_eq_mul] at hs
  nlinarith

/-- The actual Boolean generator fits the charged cube-generation schedule. -/
theorem cubeGeneration_le (S : Finset V) :
    (SpinGlass.FiniteIndexCosts.cubeExecution S.card).work ≤
      4*(S.card+1)*(2^S.card+1) := by
  have h := SpinGlass.FiniteIndexCosts.cubeExecution_work_sharp S.card
  nlinarith

theorem localControl_le (input : PreparedInput V) (edges : Finset (Finset V)) (S : Finset V)
    (hentries : input.entries.length ≤ edges.card) :
    localControl input edges S ≤ localFactor (Fintype.card V) edges.card *
      (localEvaluator edges (preparedWeight input) S).operations := by
  have hs := card_le_univ S
  have hspin := spinControl_le input edges S hentries
  have hN : 1 ≤ (Fintype.card V+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hM : 1 ≤ (edges.card+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hS : S.card+1 ≤ (Fintype.card V+1)^2 := by nlinarith
  have h2 : 1 ≤ 2^S.card := Nat.one_le_pow _ _ (by omega)
  have hfactor : 4*(S.card+1) + spinControl input edges S + 2 ≤
      localFactor (Fintype.card V) edges.card := by
    unfold localFactor
    nlinarith [Nat.mul_le_mul hN hM]
  have hbase : S.card+1 + 4*(S.card+1) ≤
      localFactor (Fintype.card V) edges.card * (S.card+1) := by
    have hF : 5 ≤ localFactor (Fintype.card V) edges.card := by
      unfold localFactor
      nlinarith [Nat.mul_le_mul hN hM]
    nlinarith
  have hprod := Nat.mul_le_mul_left (2^S.card) hfactor
  have hlow : S.card + 2^S.card + 1 ≤
      (localEvaluator edges (preparedWeight input) S).operations := by
    rw [localEvaluator_operations]
    have hx : 1 ≤ (∑ e ∈ edges.filter (fun e => e ⊆ S),
        (SpinGlass.LocalCube.localIncidence S e).card) + 3*(edges.filter (fun e => e ⊆ S)).card+1 := by omega
    have hm := Nat.mul_le_mul_left (2^S.card) hx
    nlinarith
  have hbound := Nat.mul_le_mul_left (localFactor (Fintype.card V) edges.card) hlow
  unfold localControl
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, smul_eq_mul]
  nlinarith

/-- Subset generation and each signed support-transform summand are charged
separately. Computing its parity/sign uses at most the ambient vertex count. -/
def supportControl (input : PreparedInput V) (edges : Finset (Finset V)) (U : Finset V) : ℕ :=
  4*(Fintype.card V+1)^2*U.powerset.card +
    ∑ S ∈ U.powerset, (localControl input edges S + Fintype.card V + 2)

/-- The actual all-subset generator fits the charged support-generation term. -/
theorem supportGeneration_le (U : Finset V) :
    (SpinGlass.FiniteIndexCosts.allExecution U.toList).work ≤
      4*(Fintype.card V+1)^2*U.powerset.card := by
  have h := SpinGlass.FiniteIndexCosts.allExecution_work_ambient U.toList
    (by simpa using card_le_univ U)
  simpa only [length_toList, card_powerset] using h

def supportFactor (N M : ℕ) : ℕ := localFactor N M + 10*(N+1)^2

theorem supportControl_le (input : PreparedInput V) (edges : Finset (Finset V)) (U : Finset V)
    (hentries : input.entries.length ≤ edges.card) :
    supportControl input edges U ≤ supportFactor (Fintype.card V) edges.card *
      (supportEvaluator edges (preparedWeight input) U).operations := by
  rw [supportEvaluator_operations, mul_sum]
  unfold supportControl
  have heq : 4*(Fintype.card V+1)^2*U.powerset.card +
      ∑ S ∈ U.powerset, (localControl input edges S + Fintype.card V + 2) =
      ∑ S ∈ U.powerset, (localControl input edges S + Fintype.card V + 2 +
        4*(Fintype.card V+1)^2) := by simp [sum_add_distrib]; ring
  rw [heq]
  apply sum_le_sum
  intro S hS
  have hl := localControl_le input edges S hentries
  have hN : 1 ≤ (Fintype.card V+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold supportFactor
  nlinarith

/-- The bounded support generator follows the pruned cardinality recursion.
The recorded generation work is proved output-sensitive in FiniteIndexCosts. -/
def higherControl (p cutoff : ℕ) (input : PreparedInput V) : ℕ :=
  cutoff+1 + ∑ v ∈ range (cutoff+1),
    (SpinGlass.FiniteIndexCosts.chooseWork (Fintype.card V) v +
      ∑ U ∈ (univ : Finset V).powersetCard v,
        (supportControl input ((univ : Finset V).powersetCard p) U + 3))

def higherFactor (N M : ℕ) : ℕ := supportFactor N M + 4*(N+1)^2+3

theorem higherControl_le (p cutoff : ℕ) (input : PreparedInput V)
    (hentries : input.entries.length ≤ ((univ : Finset V).powersetCard p).card)
    (hcut : cutoff ≤ Fintype.card V) :
    higherControl p cutoff input ≤ higherFactor (Fintype.card V)
      ((univ : Finset V).powersetCard p).card *
      (higherEvaluator p cutoff (preparedWeight input)).operations := by
  unfold higherControl
  rw [higherEvaluator, sumFinset_operations]
  have hinner : ∀ v ∈ range (cutoff+1),
      SpinGlass.FiniteIndexCosts.chooseWork (Fintype.card V) v +
        ∑ U ∈ (univ : Finset V).powersetCard v,
          (supportControl input ((univ : Finset V).powersetCard p) U + 3) ≤
      higherFactor (Fintype.card V) ((univ : Finset V).powersetCard p).card *
        (sumFinset ((univ : Finset V).powersetCard v)
          (supportEvaluator ((univ : Finset V).powersetCard p) (preparedWeight input))).operations := by
    intro v hv
    have hvN : v ≤ Fintype.card V := by have := mem_range.mp hv; omega
    have hg := SpinGlass.FiniteIndexCosts.chooseWork_le hvN
    rw [sumFinset_operations, mul_add, mul_sum]
    have hs : (∑ U ∈ (univ : Finset V).powersetCard v,
        (supportControl input ((univ : Finset V).powersetCard p) U+3)) ≤
        ∑ U ∈ (univ : Finset V).powersetCard v,
          (higherFactor (Fintype.card V) ((univ : Finset V).powersetCard p).card *
            (supportEvaluator ((univ : Finset V).powersetCard p) (preparedWeight input) U).operations + 3) := by
      apply sum_le_sum
      intro U hU
      have hh := supportControl_le input ((univ : Finset V).powersetCard p) U hentries
      have hf : supportFactor (Fintype.card V) ((univ : Finset V).powersetCard p).card ≤
          higherFactor (Fintype.card V) ((univ : Finset V).powersetCard p).card := by
        unfold higherFactor; omega
      exact Nat.add_le_add_right (hh.trans (Nat.mul_le_mul_right _ hf)) 3
    simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at hs
    simp only [card_powersetCard, card_univ, sum_add_distrib, sum_const, smul_eq_mul, mul_one] at hs ⊢
    unfold higherFactor at hs ⊢
    nlinarith
  have hs := sum_le_sum hinner
  rw [← mul_sum] at hs
  have hf : 1 ≤ higherFactor (Fintype.card V) ((univ : Finset V).powersetCard p).card := by
    unfold higherFactor; omega
  simp only [card_range]
  nlinarith

theorem higherFactor_le (N M : ℕ) : higherFactor N M ≤ 40*(N+1)^2*(M+1)^2 := by
  have hN : 1 ≤ (N+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hM : 1 ≤ (M+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold higherFactor supportFactor localFactor
  nlinarith [Nat.mul_le_mul hN hM, Nat.mul_le_mul_left ((N+1)^2) hM]

/-- Input generation, preparation and prefactor traversals, the integer
cutoff scan up to N, and fixed budget/branch/output decisions. -/
def setupControl (p N : ℕ) : ℕ :=
  SpinGlass.FiniteIndexCosts.chooseWork N p + (p+1) +
    10*(N.choose p+1) + 10*(N+1) + 20

theorem setupControl_le {p N : ℕ} (hpN : p ≤ N) :
    setupControl p N ≤ 100*(N+1)^2*(N.choose p+1)^2 := by
  have hgen := SpinGlass.FiniteIndexCosts.chooseWork_le hpN
  have hN : 1 ≤ (N+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hM : 1 ≤ (N.choose p+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hNN : N+1 ≤ (N+1)^2 := by nlinarith
  have hMM : N.choose p+1 ≤ (N.choose p+1)^2 := by nlinarith
  have hMN := Nat.mul_le_mul_left ((N+1)^2) hMM
  have hNQ := Nat.mul_le_mul_left ((N+1)^2) hM
  have hMQ := Nat.mul_le_mul_right ((N.choose p+1)^2) hN
  unfold setupControl
  nlinarith

/-- The concrete floor search is covered by the reserved initialization budget;
no uncharged floor oracle is needed. -/
theorem floorSearch_le_setup {p N : ℕ} {B : ℝ}
    (hp : 3 ≤ p) (hB : 0 < B) (hBT : B < betaThreshold p) :
    (SpinGlass.RoundingExecution.floorSearch N (alpha p B)).operations ≤ setupControl p N := by
  have h := valid hp hB hBT
  have hf := SpinGlass.RoundingExecution.floorSearch_operations_le N h.alpha_pos.le h.alpha_le
  unfold setupControl
  omega

/-- Branching uses the very same selected cutoff as the value computation. -/
def cachedControl (p N : ℕ) (B u : ℝ) (input : PreparedInput (Fin N)) : ℕ :=
  if SpinGlass.HigherOrderAlgorithm.exactBranch p N B u then
    localControl input ((univ : Finset (Fin N)).powersetCard p) univ
  else higherControl p (SpinGlass.HigherOrderAlgorithm.selectedSize p N B u - 1) input

theorem cachedControl_le {p N : ℕ} {B beta u : ℝ}
    (hp : 3 ≤ p) (hpN : p ≤ N) (hB : 0 < B)
    (hBT : B < SpinGlass.DesignConstants.betaThreshold p) (hu : 0 < u) (hu1 : u < 1)
    (J : Finset (Fin N) → ℝ) :
    cachedControl p N B u (prepareInput p beta J) ≤
      40*(N+1)^2*(N.choose p+1)^2 *
        (cachedEvaluator p N B u (prepareInput p beta J)).operations := by
  have hentries : (prepareInput p beta J).entries.length ≤
      ((univ : Finset (Fin N)).powersetCard p).card := by simp [prepareInput]
  unfold cachedControl cachedEvaluator
  split_ifs with he
  · have h := localControl_le (prepareInput p beta J)
      ((univ : Finset (Fin N)).powersetCard p) univ hentries
    have hf : localFactor N (N.choose p) ≤ 40*(N+1)^2*(N.choose p+1)^2 := by
      unfold localFactor; nlinarith
    simp only [Fintype.card_fin, card_powersetCard, card_univ] at h
    exact h.trans (Nat.mul_le_mul_right _ hf)
  · have hcut : selectedSize p N B u - 1 ≤ N := by
      have hv := valid hp hB hBT
      have hs := selectedSize_spec hp hB hBT hu hu1 he
      have hfloor : (Nat.floor (alpha p B * N) : ℝ) ≤ alpha p B * N :=
        Nat.floor_le (mul_nonneg hv.alpha_pos.le (Nat.cast_nonneg _))
      have hm : (selectedSize p N B u : ℝ) ≤ Nat.floor (alpha p B * N) := by exact_mod_cast hs.2.1
      have ha := mul_le_mul_of_nonneg_right hv.alpha_le (Nat.cast_nonneg N : (0:ℝ) ≤ N)
      have hmN : (selectedSize p N B u : ℝ) ≤ N := by nlinarith
      have hmNnat : selectedSize p N B u ≤ N := by exact_mod_cast hmN
      omega
    have h := higherControl_le p (selectedSize p N B u - 1) (prepareInput p beta J)
      hentries (by simpa using hcut)
    simp only [Fintype.card_fin, card_powersetCard, card_univ] at h
    exact h.trans (Nat.mul_le_mul_right _ (higherFactor_le N (N.choose p)))

end SpinGlass.HigherOrderControl
