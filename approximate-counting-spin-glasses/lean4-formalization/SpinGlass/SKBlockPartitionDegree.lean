import SpinGlass.SKBlockPartition

/-! Exact outside-degree preservation and the canonical block-selection equivalence. -/
noncomputable section
namespace SpinGlass.SKBlockPartition
open scoped BigOperators
open SpinGlass.SKComponents
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- Every used outside vertex has exactly its original degree in its unique block. -/
theorem block_degree_exact (incidence : E → Finset V) (A : Finset V) (Γ : Finset E)
    {K : Finset E} (hK : K ∈ blockFamily incidence A Γ)
    {v : V} (hv : v ∈ outside incidence A K) :
    SpinGlass.Expansion.degree incidence K v = SpinGlass.Expansion.degree incidence Γ v := by
  rw [blockFamily_eq_image] at hK
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨hvU, hvA⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨g, hg, hgv⟩ := Finset.mem_biUnion.mp hvU
  have hgΓ := plainComponent_subset incidence A Γ e hg
  have heg := (mem_plainComponent incidence A Γ e ⟨g, hgΓ⟩).mp hg
  unfold SpinGlass.Expansion.degree
  congr 1
  ext f
  simp only [Finset.mem_filter]
  constructor
  · exact fun hf => ⟨plainComponent_subset incidence A Γ e hf.1, hf.2⟩
  · intro hf
    refine ⟨(mem_plainComponent incidence A Γ e ⟨f, hf.1⟩).mpr ?_, hf.2⟩
    exact related_trans incidence A Γ heg
      (related_of_shared_outside incidence A Γ ⟨g, hgΓ⟩ ⟨f, hf.1⟩ v hvA hgv hf.2)

/-- Outside support is monotone under inclusion of actual edge sets. -/
theorem outside_mono (incidence : E → Finset V) (A : Finset V)
    {K Γ : Finset E} (hsub : K ⊆ Γ) : outside incidence A K ⊆ outside incidence A Γ := by
  intro v hv
  obtain ⟨hvU, hvA⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨e, he, hev⟩ := Finset.mem_biUnion.mp hvU
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨e, hsub he, hev⟩, hvA⟩

/-- The exact condition satisfied by every primitive's used outside vertices. -/
def OutsideDegreeTwo (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) : Prop :=
  ∀ v ∈ outside incidence A Γ, SpinGlass.Expansion.degree incidence Γ v = 2

/-- The original graph's outside-degree condition passes to every canonical block. -/
theorem block_outside_degree_two (incidence : E → Finset V) (A : Finset V) (Γ : Finset E)
    (hΓ : OutsideDegreeTwo incidence A Γ) {K : Finset E}
    (hK : K ∈ blockFamily incidence A Γ) : OutsideDegreeTwo incidence A K := by
  intro v hv
  rw [block_degree_exact incidence A Γ hK hv]
  exact hΓ v (outside_mono incidence A (blockFamily_subset incidence A Γ hK) hv)

/-- Nonempty internally connected and mutually outside-disjoint block selections. -/
structure ValidSelection (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E)) : Prop where
  nonempty : ∀ K ∈ F, K.Nonempty
  connected : ∀ K ∈ F, Connected incidence A K
  outside_disjoint : (F : Set (Finset E)).PairwiseDisjoint (outside incidence A)

theorem canonical_valid (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) :
    ValidSelection incidence A (blockFamily incidence A Γ) :=
  ⟨fun _ => blockFamily_nonempty incidence A Γ,
    fun _ => blockFamily_connected incidence A Γ, blockFamily_outside_disjoint incidence A Γ⟩

/-- The canonical partition is an actual two-sided inverse of block union. -/
def selectionEquivGraphs (incidence : E → Finset V) (A : Finset V) :
    {F : Finset (Finset E) // ValidSelection incidence A F} ≃ Finset E where
  toFun F := F.val.biUnion id
  invFun Γ := ⟨blockFamily incidence A Γ, canonical_valid incidence A Γ⟩
  left_inv F := Subtype.ext (blockFamily_biUnion incidence A F.val
    F.property.nonempty F.property.connected F.property.outside_disjoint)
  right_inv Γ := blockFamily_cover incidence A Γ

/-- Exact degree preservation also holds for a block in any valid selection. -/
theorem selected_degree_exact (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E)) (hF : ValidSelection incidence A F)
    {K : Finset E} (hK : K ∈ F) {v : V} (hv : v ∈ outside incidence A K) :
    SpinGlass.Expansion.degree incidence K v =
      SpinGlass.Expansion.degree incidence (F.biUnion id) v := by
  apply block_degree_exact incidence A (F.biUnion id) _ hv
  rw [blockFamily_biUnion incidence A F hF.nonempty hF.connected hF.outside_disjoint]
  exact hK

/-- Conversely, the union of valid degree-two blocks has exactly degree two at
every used outside vertex. -/
theorem union_outside_degree_two (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E)) (hF : ValidSelection incidence A F)
    (hdegree : ∀ K ∈ F, OutsideDegreeTwo incidence A K) :
    OutsideDegreeTwo incidence A (F.biUnion id) := by
  intro v hv
  obtain ⟨hvU, hvA⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨e, he, hev⟩ := Finset.mem_biUnion.mp hvU
  obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.mp he
  have hvK : v ∈ outside incidence A K :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨e, heK, hev⟩, hvA⟩
  rw [← selected_degree_exact incidence A F hF hK hvK]
  exact hdegree K hK v hvK

/-- The natural outside-degree restriction is preserved in both directions of
the exact canonical selection equivalence. -/
theorem union_outside_degree_two_iff (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E)) (hF : ValidSelection incidence A F) :
    OutsideDegreeTwo incidence A (F.biUnion id) ↔
      ∀ K ∈ F, OutsideDegreeTwo incidence A K := by
  constructor
  · intro hΓ K hK
    apply block_outside_degree_two incidence A (F.biUnion id) hΓ
    rw [blockFamily_biUnion incidence A F hF.nonempty hF.connected hF.outside_disjoint]
    exact hK
  · exact union_outside_degree_two incidence A F hF

/-- Restricting the bijection to degree-two outside graphs remains an actual equivalence. -/
def degreeTwoSelectionEquivGraphs (incidence : E → Finset V) (A : Finset V) :
    {F : Finset (Finset E) // ValidSelection incidence A F ∧
      ∀ K ∈ F, OutsideDegreeTwo incidence A K} ≃
      {Γ : Finset E // OutsideDegreeTwo incidence A Γ} where
  toFun F := ⟨F.val.biUnion id, union_outside_degree_two incidence A F.val F.property.1 F.property.2⟩
  invFun Γ := ⟨blockFamily incidence A Γ.val, canonical_valid incidence A Γ.val,
    fun K hK => block_outside_degree_two incidence A Γ.val Γ.property hK⟩
  left_inv F := Subtype.ext (blockFamily_biUnion incidence A F.val
    F.property.1.nonempty F.property.1.connected F.property.1.outside_disjoint)
  right_inv Γ := Subtype.ext (blockFamily_cover incidence A Γ.val)

end SpinGlass.SKBlockPartition
