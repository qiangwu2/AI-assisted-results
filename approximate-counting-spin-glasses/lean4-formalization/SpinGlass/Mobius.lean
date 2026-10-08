import SpinGlass.Support
import SpinGlass.Expansion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Exact-support extraction by finite Möbius inversion

The cancellation kernel is proved here by complementing subsets and expanding
`(1 + (-1))^n`. No inversion identity is assumed. The final specialization uses
actual finite simple hypergraphs and their vertex union as support. The weights
are arbitrary elements of a commutative ring, so signed real weights are covered.
-/

namespace SpinGlass.Mobius

variable {V I R : Type*} [DecidableEq V] [CommRing R]

/-- The alternating sum over all subsets cancels unless the ground set is empty. -/
theorem alternating_powerset_sum (U : Finset V) :
    (∑ S ∈ U.powerset, (-1 : R) ^ S.card) = if U = ∅ then 1 else 0 := by
  have h := Finset.sum_pow_mul_eq_add_pow (-1 : R) 1 U
  simp only [one_pow, mul_one, neg_add_cancel] at h
  rw [h]
  by_cases hU : U = ∅ <;> simp [hU]

/-- Complementation converts the subsets containing `T` into subsets of `U \ T`. -/
theorem superset_alternating_sum (T U : Finset V) (hTU : T ⊆ U) :
    (∑ S ∈ U.powerset with T ⊆ S, (-1 : R) ^ (U.card - S.card)) =
      if T = U then 1 else 0 := by
  calc
    (∑ S ∈ U.powerset with T ⊆ S, (-1 : R) ^ (U.card - S.card)) =
        ∑ D ∈ (U \ T).powerset, (-1 : R) ^ D.card := by
      apply Finset.sum_bij (fun S _ => U \ S)
      · intro S hS
        exact Finset.mem_powerset.mpr
          (Finset.sdiff_subset_sdiff_right U (Finset.mem_filter.mp hS).2)
      · intro S hS W hW heq
        have hSU := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
        have hWU := Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1
        have h := congrArg (fun B => U \ B) heq
        simpa only [Finset.sdiff_sdiff_eq_self hSU,
          Finset.sdiff_sdiff_eq_self hWU] using h
      · intro D hD
        have hDT : D ⊆ U \ T := Finset.mem_powerset.mp hD
        have hDU : D ⊆ U := Finset.Subset.trans hDT Finset.sdiff_subset
        refine ⟨U \ D, ?_, Finset.sdiff_sdiff_eq_self hDU⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
        intro v hv
        apply Finset.mem_sdiff.mpr
        refine ⟨hTU hv, ?_⟩
        intro hvD
        exact (Finset.mem_sdiff.mp (hDT hvD)).2 hv
      · intro S hS
        rw [Finset.card_sdiff_of_subset
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)]
    _ = if U \ T = ∅ then 1 else 0 := alternating_powerset_sum (U \ T)
    _ = if T = U then 1 else 0 := by
      by_cases hEq : T = U
      · simp [hEq]
      · have hne : U \ T ≠ ∅ := by
          intro hempty
          exact hEq (Finset.Subset.antisymm hTU
            (Finset.sdiff_eq_empty_iff_subset.mp hempty))
        simp [hne, hEq]

/-- The Möbius kernel isolates exactly one support, including outside supports. -/
theorem subset_cancellation (T U : Finset V) :
    (∑ S ∈ U.powerset,
      if T ⊆ S then (-1 : R) ^ (U.card - S.card) else 0) =
      if T = U then 1 else 0 := by
  by_cases hTU : T ⊆ U
  · simpa only [Finset.sum_filter] using
      (superset_alternating_sum (R := R) T U hTU)
  · have hsum : (∑ S ∈ U.powerset,
        if T ⊆ S then (-1 : R) ^ (U.card - S.card) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      apply if_neg
      intro hTS
      exact hTU (Finset.Subset.trans hTS (Finset.mem_powerset.mp hS))
    have hne : T ≠ U := by
      intro heq
      subst T
      exact hTU Finset.Subset.rfl
    simp [hsum, hne]

/-- Total weight of objects whose supports are contained in a prescribed set. -/
def containedSum [DecidableEq I] (family : Finset I) (support : I → Finset V)
    (weight : I → R) (U : Finset V) : R :=
  ∑ i ∈ family with support i ⊆ U, weight i

/-- Total weight of objects whose supports equal a prescribed set. -/
def exactSupportSum [DecidableEq I] (family : Finset I) (support : I → Finset V)
    (weight : I → R) (U : Finset V) : R :=
  ∑ i ∈ family with support i = U, weight i

/-- The paper's alternating subset transform. -/
def transform (G : Finset V → R) (U : Finset V) : R :=
  ∑ S ∈ U.powerset, (-1 : R) ^ (U.card - S.card) * G S

/-- Exact-support inversion for an arbitrary finite weighted family. -/
theorem transform_containedSum [DecidableEq I] (family : Finset I)
    (support : I → Finset V) (weight : I → R) (U : Finset V) :
    transform (containedSum family support weight) U =
      exactSupportSum family support weight U := by
  unfold transform containedSum exactSupportSum
  simp_rw [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrArg (fun a : R => a * weight i)
    (subset_cancellation (R := R) (support i) U)
  simpa only [Finset.sum_mul, ite_mul, zero_mul, one_mul] using h

/-- The induced-support graph sum `G(U)`, with actual hypergraph vertex support. -/
def G (family : Finset (Hypergraph.FiniteHypergraph V))
    (weight : Hypergraph.FiniteHypergraph V → R) (U : Finset V) : R :=
  containedSum family Hypergraph.support weight U

/-- The paper's exact-support transform `A(U)`. -/
def A (family : Finset (Hypergraph.FiniteHypergraph V))
    (weight : Hypergraph.FiniteHypergraph V → R) (U : Finset V) : R :=
  transform (G family weight) U

/-- The alternating transform selects exactly the hypergraphs with vertex support `U`.
The family may, for example, be restricted to even hypergraphs before this operation. -/
theorem A_eq_exact_support (family : Finset (Hypergraph.FiniteHypergraph V))
    (weight : Hypergraph.FiniteHypergraph V → R) (U : Finset V) :
    A family weight U = ∑ Γ ∈ family with Hypergraph.support Γ = U, weight Γ := by
  exact transform_containedSum family Hypergraph.support weight U

/-- Selecting only edges inside `U` is equivalent to restricting the actual graph support. -/
theorem subset_induced_iff (edges Γ : Hypergraph.FiniteHypergraph V) (U : Finset V) :
    Γ ⊆ edges.filter (fun e => e ⊆ U) ↔ Γ ⊆ edges ∧ Hypergraph.support Γ ⊆ U := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro e he
      exact (Finset.mem_filter.mp (h he)).1
    · rw [Hypergraph.support, Finset.biUnion_subset]
      intro e he
      exact (Finset.mem_filter.mp (h he)).2
  · rintro ⟨hΓ, hU⟩ e he
    apply Finset.mem_filter.mpr
    refine ⟨hΓ he, ?_⟩
    exact (Finset.biUnion_subset.mp hU) e he

section SpinPolynomial

variable [Fintype V]

/-- The even selected edge families inside `U` are precisely the even ambient
families whose graph support lies inside `U`. -/
theorem even_induced_family (edges : Hypergraph.FiniteHypergraph V) (U : Finset V) :
    (edges.filter (fun e => e ⊆ U)).powerset.filter (Expansion.IsEven id) =
      (edges.powerset.filter (Expansion.IsEven id)).filter
        (fun Γ => Hypergraph.support Γ ⊆ U) := by
  ext Γ
  simp only [Finset.mem_filter, Finset.mem_powerset, subset_induced_iff]
  exact and_right_comm

/-- The normalized ambient-cube spin polynomial on interactions contained in `U`.
Unused spin coordinates remain in this average; reducing the enumerated spin
cube to the vertices of `U` is not asserted here. -/
noncomputable def Gspin (edges : Hypergraph.FiniteHypergraph V)
    (weight : Finset V → ℝ) (U : Finset V) : ℝ :=
  Expansion.spinMean (fun σ : V → Bool =>
    ∏ e ∈ edges.filter (fun e => e ⊆ U),
      (1 + weight e * Expansion.edgeCharacter id σ e))

/-- The actual spin polynomial equals the contained-support sum over even graphs. -/
theorem Gspin_eq_G (edges : Hypergraph.FiniteHypergraph V)
    (weight : Finset V → ℝ) (U : Finset V) :
    Gspin edges weight U =
      G (edges.powerset.filter (Expansion.IsEven id))
        (fun Γ => ∏ e ∈ Γ, weight e) U := by
  unfold Gspin
  rw [Expansion.graphical_expansion, even_induced_family]
  rfl

/-- Applying the alternating support transform to actual spin averages selects
exactly the even hypergraphs with vertex support `U`. -/
theorem transform_Gspin_eq_exact_support (edges : Hypergraph.FiniteHypergraph V)
    (weight : Finset V → ℝ) (U : Finset V) :
    transform (Gspin edges weight) U =
      ∑ Γ ∈ (edges.powerset.filter (Expansion.IsEven id)) with
        Hypergraph.support Γ = U, ∏ e ∈ Γ, weight e := by
  have heq : Gspin edges weight =
      G (edges.powerset.filter (Expansion.IsEven id)) (fun Γ => ∏ e ∈ Γ, weight e) := by
    funext S
    exact Gspin_eq_G edges weight S
  rw [heq]
  exact A_eq_exact_support _ _ U

end SpinPolynomial

end SpinGlass.Mobius
