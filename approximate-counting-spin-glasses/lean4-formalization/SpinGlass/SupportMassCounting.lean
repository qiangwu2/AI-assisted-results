import SpinGlass.UniformMass
import SpinGlass.Support
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Counting the actual support-restricted even-hypergraph family

The weighted count is bounded by choosing its actual vertex support, then
counting edge subsets subject only to the proved minimum-edge constraint.
-/

noncomputable section
namespace SpinGlass.SupportMassCounting
open Finset Real
open SpinGlass.Expansion SpinGlass.Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every even simple p-uniform hypergraph on the ambient vertex set. -/
def evenGraphs (p : ℕ) : Finset (Finset (Finset V)) :=
  ((Finset.univ : Finset V).powersetCard p).powerset.filter (IsEven id)

/-- The exact family whose used support has the prescribed size. -/
def supportFamily (p v : ℕ) : Finset (Finset (Finset V)) :=
  (evenGraphs p).filter (fun Γ => (support Γ).card = v)

/-- The paper's positive squared mass at a fixed support size. -/
def supportMass (p v : ℕ) (r : ℝ) : ℝ :=
  ∑ Γ ∈ (supportFamily p v : Finset (Finset (Finset V))), r^Γ.card

/-- The least possible edge count forced by the even-degree constraint. -/
def minEdges (p v : ℕ) : ℕ := Nat.ceil ((2 : ℝ) * v / p)

theorem evenGraphs_uniform {p : ℕ} {Γ : Finset (Finset V)} (hΓ : Γ ∈ evenGraphs p) :
    ∀ e ∈ Γ, e.card = p := by
  intro e he
  exact (Finset.mem_powersetCard.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hΓ).1) he)).2

theorem twice_support_le_edges {p : ℕ} {Γ : Finset (Finset V)} (hΓ : Γ ∈ evenGraphs p) :
    2 * (support Γ).card ≤ p * Γ.card := by
  apply SpinGlass.Hypergraph.twice_support_le_uniform_edge_count Γ p
    (evenGraphs_uniform hΓ)
  intro v hv
  have he := (Finset.mem_filter.mp hΓ).2 v
  exact Nat.even_iff.mp he

theorem minEdges_le_card {p v : ℕ} (hp : 0 < p) {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ supportFamily p v) : minEdges p v ≤ Γ.card := by
  have hG := (Finset.mem_filter.mp hΓ).1
  have hv := (Finset.mem_filter.mp hΓ).2
  have h := twice_support_le_edges hG
  rw [hv] at h
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (Nat.cast_pos.mpr hp)).mpr
  exact_mod_cast (by simpa only [Nat.mul_comm p Γ.card] using h)

/-- Positive supports smaller than one interaction carry exactly zero mass. -/
theorem supportMass_eq_zero_of_lt {p v : ℕ} (hv : 0 < v) (hvp : v < p) (r : ℝ) :
    supportMass (V := V) p v r = 0 := by
  have hempty : (supportFamily p v : Finset (Finset (Finset V))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Γ hΓ
    obtain ⟨hG, hcard⟩ := Finset.mem_filter.mp hΓ
    have hne : Γ.Nonempty := by
      by_contra h
      have hzero : Γ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst Γ
      simp [support] at hcard
      omega
    obtain ⟨e, he⟩ := hne
    have hsub : e ⊆ support Γ := by
      intro x hx
      exact mem_support_iff.mpr ⟨e, he, hx⟩
    have hc := Finset.card_le_card hsub
    rw [evenGraphs_uniform hG e he, hcard] at hc
    omega
  simp [supportMass, hempty]

/-- Edge subsets of a given finite set, grouped by their exact cardinality. -/
theorem weighted_powerset_tail {E : Type*} [DecidableEq E] (edges : Finset E)
    (m : ℕ) (r : ℝ) :
    (∑ Γ ∈ edges.powerset.filter (fun Γ => m ≤ Γ.card), r^Γ.card) =
      ∑ k ∈ (Finset.range (edges.card + 1)).filter (fun k => m ≤ k),
        (edges.card.choose k : ℝ) * r^k := by
  rw [Finset.sum_filter, Finset.sum_powerset]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  have heq : ∀ Γ ∈ edges.powersetCard k,
      (if m ≤ Γ.card then r^Γ.card else 0) = if m ≤ k then r^k else 0 := by
    intro Γ hΓ
    rw [(Finset.mem_powersetCard.mp hΓ).2]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_powersetCard]
  split_ifs <;> simp [nsmul_eq_mul]

/-- The exact support-selection and binomial edge-count upper bound (49). -/
theorem supportMass_le_binomial_tail {p v : ℕ} (hp : 0 < p) {r : ℝ} (hr : 0 ≤ r) :
    supportMass (V := V) p v r ≤ (Fintype.card V).choose v *
      ∑ k ∈ (Finset.range (v.choose p + 1)).filter (fun k => minEdges p v ≤ k),
        ((v.choose p).choose k : ℝ) * r^k := by
  classical
  have hmap : ∀ Γ ∈ (supportFamily p v : Finset (Finset (Finset V))),
      support Γ ∈ (Finset.univ : Finset V).powersetCard v := by
    intro Γ hΓ
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hΓ).2⟩
  unfold supportMass
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun Γ => r^Γ.card)]
  have hbound : ∀ S ∈ (Finset.univ : Finset V).powersetCard v,
      (∑ Γ ∈ (supportFamily p v : Finset (Finset (Finset V))).filter (fun Γ => support Γ = S), r^Γ.card) ≤
      ∑ k ∈ (Finset.range (v.choose p + 1)).filter (fun k => minEdges p v ≤ k),
        ((v.choose p).choose k : ℝ) * r^k := by
    intro S hS
    have hSv := (Finset.mem_powersetCard.mp hS).2
    have hsub : (supportFamily p v : Finset (Finset (Finset V))).filter (fun Γ => support Γ = S) ⊆
        (S.powersetCard p).powerset.filter (fun Γ => minEdges p v ≤ Γ.card) := by
      intro Γ hΓ
      obtain ⟨hfamily, hsupp⟩ := Finset.mem_filter.mp hΓ
      refine Finset.mem_filter.mpr ⟨?_, minEdges_le_card hp hfamily⟩
      apply Finset.mem_powerset.mpr
      intro e he
      refine Finset.mem_powersetCard.mpr ⟨?_, evenGraphs_uniform (Finset.mem_filter.mp hfamily).1 e he⟩
      intro x hx
      rw [← hsupp]
      exact mem_support_iff.mpr ⟨e, he, hx⟩
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun Γ _ _ => pow_nonneg hr Γ.card)
    rw [weighted_powerset_tail, Finset.card_powersetCard, hSv] at h
    exact h
  calc
    _ ≤ ∑ _S ∈ (Finset.univ : Finset V).powersetCard v,
      ∑ k ∈ (Finset.range (v.choose p + 1)).filter (fun k => minEdges p v ≤ k),
        ((v.choose p).choose k : ℝ) * r^k := Finset.sum_le_sum hbound
    _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul]

end SpinGlass.SupportMassCounting
