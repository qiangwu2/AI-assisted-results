import SpinGlass.SKBlockProduct
import SpinGlass.SKPrimitiveExpansion

/-! # The exact graph sum of an optional connected-block product -/
noncomputable section
namespace SpinGlass.SKGraphProduct
open scoped BigOperators
open SKRing SKGraphMonomial SKBlockPartition SKBlockProduct
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
attribute [local instance] Classical.propDecidable

/-- Color reuse between two graph pieces annihilates their product. -/
theorem value_mul_zero_of_color_overlap {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (K H : Finset E)
    (hc : ¬ Disjoint (colors incidence A χ K) (colors incidence A χ H)) :
    value incidence A branch χ w K * value incidence A branch χ w H = 0 := by
  classical
  unfold value
  split
  next hK =>
    split
    next hcK =>
      split
      next hH =>
        split
        next hcH =>
          apply ext
          apply SKCoefficient.mul_single_single_rejected
          exact fun h => hc h.2
        next hcH => simp
      next hH => simp
    next hcK => simp
  next hK => simp

/-- In particular, any repeated outside vertex annihilates the selected pair. -/
theorem value_mul_zero_of_outside_overlap {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (K H : Finset E)
    (hc : ¬ Disjoint (SKGraphMonomial.outside incidence A K) (SKGraphMonomial.outside incidence A H)) :
    value incidence A branch χ w K * value incidence A branch χ w H = 0 := by
  apply value_mul_zero_of_color_overlap
  obtain ⟨v,hvK,hvH⟩ := Finset.not_disjoint_iff.mp hc
  exact Finset.not_disjoint_iff.mpr ⟨χ v,
    Finset.mem_image.mpr ⟨v,hvK,rfl⟩, Finset.mem_image.mpr ⟨v,hvH,rfl⟩⟩

/-- A product containing an annihilated pair is itself zero. -/
theorem product_eq_zero_of_pair {R I : Type*} [CommRing R] [DecidableEq I]
    (F : Finset I) (f : I → R) {a c : I} (ha : a ∈ F) (hc : c ∈ F)
    (hac : a ≠ c) (hzero : f a * f c = 0) : ∏ i ∈ F, f i = 0 := by
  rw [← Finset.mul_prod_erase F f ha]
  have hc' : c ∈ F.erase a := Finset.mem_erase.mpr ⟨Ne.symm hac,hc⟩
  rw [← Finset.mul_prod_erase (F.erase a) f hc', ← mul_assoc, hzero, zero_mul]

/-- Invalid overlap selections vanish, without requiring their weights positive. -/
theorem product_value_zero_of_invalid {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (F : Finset (Finset E))
    (hne : ∀ K ∈ F, K.Nonempty) (hconn : ∀ K ∈ F, Connected incidence A K)
    (hF : ¬ ValidSelection incidence A F) :
    (∏ K ∈ F, value incidence A branch χ w K) = 0 := by
  have hd : ¬ (F : Set (Finset E)).PairwiseDisjoint (SKBlockPartition.outside incidence A) :=
    fun h => hF ⟨hne,hconn,h⟩
  simp only [Set.PairwiseDisjoint, Set.Pairwise] at hd
  push_neg at hd
  obtain ⟨K,hK,H,hH,hneKH,hover⟩ := hd
  exact product_eq_zero_of_pair F _ hK hH hneKH
    (value_mul_zero_of_outside_overlap incidence A branch χ w K H hover)

/-- Canonical block membership is the exact image predicate for valid selections. -/
def BuiltFrom (incidence : E → Finset V) (A : Finset V)
    (Q : Finset (Finset E)) (Γ : Finset E) : Prop := blockFamily incidence A Γ ⊆ Q

/-- Every connected-piece optional product sums each graph once, through the
canonical decomposition actually proved from outside-edge adjacency. -/
theorem optional_product_eq_graph_sum [Fintype E] {b L : ℕ}
    (incidence : E → Finset V) (A : Finset V) (branch : Fin b → V)
    (χ : V → Fin L) (w : E → ℝ) (Q : Finset (Finset E))
    (hne : ∀ K ∈ Q, K.Nonempty) (hconn : ∀ K ∈ Q, Connected incidence A K) :
    (∏ K ∈ Q, (1 + value incidence A branch χ w K)) =
      ∑ Γ ∈ (Finset.univ : Finset (Finset E)).filter (BuiltFrom incidence A Q),
        value incidence A branch χ w Γ := by
  classical
  rw [Finset.prod_one_add]
  have hfilt : (∑ F ∈ Q.powerset, ∏ K ∈ F, value incidence A branch χ w K) =
      ∑ F ∈ Q.powerset.filter (ValidSelection incidence A),
        ∏ K ∈ F, value incidence A branch χ w K := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro F hF
    by_cases hv : ValidSelection incidence A F
    · simp [hv]
    · rw [if_neg hv]
      exact product_value_zero_of_invalid incidence A branch χ w F
        (fun K hK => hne K ((Finset.mem_powerset.mp hF) hK))
        (fun K hK => hconn K ((Finset.mem_powerset.mp hF) hK)) hv
  rw [hfilt]
  apply Finset.sum_bij (fun F _ => F.biUnion id)
  · intro F hF
    obtain ⟨hsub,hvalid⟩ := Finset.mem_filter.mp hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, BuiltFrom]
    rw [blockFamily_biUnion incidence A F hvalid.nonempty hvalid.connected hvalid.outside_disjoint]
    exact Finset.mem_powerset.mp hsub
  · intro F hF G hG heq
    have hf := (Finset.mem_filter.mp hF).2
    have hg := (Finset.mem_filter.mp hG).2
    exact selection_unique incidence A F G hf.nonempty hg.nonempty hf.connected hg.connected
      hf.outside_disjoint hg.outside_disjoint heq
  · intro Γ hΓ
    refine ⟨blockFamily incidence A Γ, ?_, blockFamily_cover incidence A Γ⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.mem_filter.mp hΓ).2,
      canonical_valid incidence A Γ⟩
  · intro F hF
    exact product_value_eq_union incidence A branch χ w F (Finset.mem_filter.mp hF).2

/-- A piece consuming an outside vertex lies in the color ideal whenever it survives. -/
theorem value_vanishesBelow {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (K : Finset E)
    (hout : (SKGraphMonomial.outside incidence A K).Nonempty) :
    SKCoefficient.VanishesBelow 1 (value incidence A branch χ w K).coeff := by
  unfold value
  split
  next hk =>
    split
    next hc =>
      apply SKPrimitiveExpansion.monomial_vanishesBelow
      exact hout.image χ
    next hc => intro z hz; rfl
  next hk => intro z hz; rfl

/-- Each actual primitive graph is square-zero, so its optional factor is exact. -/
theorem value_sq_zero {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (K : Finset E)
    (hout : (SKGraphMonomial.outside incidence A K).Nonempty) :
    value incidence A branch χ w K ^ 2 = 0 := by
  unfold value
  split
  next hk =>
    split
    next hc =>
      apply monomial_sq_zero
      exact hout.image χ
    next hc => simp
  next hk => simp

end SpinGlass.SKGraphProduct
