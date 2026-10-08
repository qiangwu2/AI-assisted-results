import SpinGlass.SKBlockPartitionDegree
import SpinGlass.SKGraphMonomial

/-! The exact ring product of actual canonical blocks. -/
noncomputable section
namespace SpinGlass.SKBlockProduct
open scoped BigOperators
open SpinGlass.SKBlockPartition
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- A subfamily of a valid block selection remains valid. -/
theorem valid_subset (incidence : E → Finset V) (A : Finset V)
    {F G : Finset (Finset E)} (hF : ValidSelection incidence A F) (hGF : G ⊆ F) :
    ValidSelection incidence A G :=
  ⟨fun K hK => hF.nonempty K (hGF hK), fun K hK => hF.connected K (hGF hK),
    fun K hK M hM hne => hF.outside_disjoint (hGF hK) (hGF hM) hne⟩

/-- A block's monomial at the empty graph is precisely the coefficient-ring unit. -/
theorem value_empty {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) :
    SpinGlass.SKGraphMonomial.value incidence A branch χ w ∅ = 1 := by
  classical
  have hc : SpinGlass.SKGraphMonomial.Colorful incidence A χ ∅ := by
    simp [SpinGlass.SKGraphMonomial.Colorful, SpinGlass.SKGraphMonomial.outside]
  simp only [SpinGlass.SKGraphMonomial.value, Finset.card_empty, Nat.zero_le, dif_pos,
    if_pos hc]
  apply SpinGlass.SKRing.ext
  change SpinGlass.SKCoefficient.single _ _ = SpinGlass.SKCoefficient.one b L
  congr 1
  · apply Prod.ext
    · apply Fin.ext
      rfl
    · apply Prod.ext
      · simp [SpinGlass.SKGraphMonomial.basis, SpinGlass.SKGraphMonomial.colors,
          SpinGlass.SKGraphMonomial.outside, SpinGlass.SKCoefficient.one, SpinGlass.SKCoefficient.oneBasis]
      · funext a
        simp [SpinGlass.SKGraphMonomial.basis, SpinGlass.Expansion.degree,
          SpinGlass.SKCoefficient.oneBasis]
        rfl

/-- Outside support commutes with the union of a block family. -/
theorem outside_biUnion (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E)) :
    outside incidence A (F.biUnion id) = F.biUnion (outside incidence A) := by
  ext v
  simp only [outside, Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨e, ⟨K, hK, he⟩, hev⟩, hvA⟩
    exact ⟨K, hK, ⟨⟨e, he, hev⟩, hvA⟩⟩
  · rintro ⟨K, hK, ⟨⟨e, he, hev⟩, hvA⟩⟩
    exact ⟨⟨e, ⟨K, hK, he⟩, hev⟩, hvA⟩

/-- Every valid selection multiplies to its actual union monomial. All signs,
edge counts, degree reductions, and color collisions are preserved exactly. -/
theorem product_value_eq_union {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ)
    (F : Finset (Finset E)) (hF : ValidSelection incidence A F) :
    (∏ K ∈ F, SpinGlass.SKGraphMonomial.value incidence A branch χ w K) =
      SpinGlass.SKGraphMonomial.value incidence A branch χ w (F.biUnion id) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (value_empty incidence A branch χ w).symm
  | @insert K F hKF ih =>
    have htail := valid_subset incidence A hF (Finset.subset_insert K F)
    have hedges := selection_edge_disjoint incidence A (insert K F)
      hF.nonempty hF.connected hF.outside_disjoint
    have he : Disjoint K (F.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro M hM
      exact hedges (Finset.mem_insert_self K F) (Finset.mem_insert_of_mem hM)
        (by intro h; exact hKF (h.symm ▸ hM))
    have ho : Disjoint (outside incidence A K) (outside incidence A (F.biUnion id)) := by
      rw [outside_biUnion, Finset.disjoint_biUnion_right]
      intro M hM
      exact hF.outside_disjoint (Finset.mem_insert_self K F) (Finset.mem_insert_of_mem hM)
        (by intro h; exact hKF (h.symm ▸ hM))
    rw [Finset.prod_insert hKF, ih htail, Finset.biUnion_insert]
    exact SpinGlass.SKGraphMonomial.value_mul incidence A branch χ w K (F.biUnion id) he ho

/-- Canonical decomposition factors the actual signed graph monomial in the
concrete dense coefficient ring. -/
theorem canonical_product {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (Γ : Finset E) :
    (∏ K ∈ blockFamily incidence A Γ,
      SpinGlass.SKGraphMonomial.value incidence A branch χ w K) =
      SpinGlass.SKGraphMonomial.value incidence A branch χ w Γ := by
  rw [product_value_eq_union incidence A branch χ w _ (canonical_valid incidence A Γ),
    blockFamily_cover]

end SpinGlass.SKBlockProduct
