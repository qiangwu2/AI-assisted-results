import SpinGlass.SKComponents

/-! The canonical ambient-edge component family and its exact reconstruction theorem. -/
noncomputable section
namespace SpinGlass.SKBlockPartition
open scoped BigOperators
open SpinGlass.SKComponents
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- A component expressed using the original edge type, with no nested subtype. -/
def plainComponent (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) (e : Γ) : Finset E :=
  (component incidence A Γ e).image Subtype.val

/-- The canonical family of ambient-edge blocks. -/
def blockFamily (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) : Finset (Finset E) :=
  (components incidence A Γ).image (fun K => K.image Subtype.val)

/-- The actual outside support of an ambient-edge block. -/
def outside (incidence : E → Finset V) (A : Finset V) (K : Finset E) : Finset V :=
  K.biUnion incidence \ A

/-- Internal connectedness uses the actual outside-edge adjacency relation. -/
def Connected (incidence : E → Finset V) (A : Finset V) (K : Finset E) : Prop :=
  ∀ e f : K, Related incidence A K e f

theorem blockFamily_eq_image (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) :
    blockFamily incidence A Γ = Finset.univ.image (plainComponent incidence A Γ) := by
  rw [blockFamily, components, Finset.image_image]
  rfl

theorem mem_plainComponent (incidence : E → Finset V) (A : Finset V) (Γ : Finset E)
    (e f : Γ) : f.val ∈ plainComponent incidence A Γ e ↔ Related incidence A Γ e f := by
  simp only [plainComponent, Finset.mem_image]
  constructor
  · rintro ⟨g, hg, heq⟩
    have hgf : g = f := Subtype.ext heq
    exact (mem_component incidence A Γ e f).mp (hgf ▸ hg)
  · intro h
    exact ⟨f, (mem_component incidence A Γ e f).mpr h, rfl⟩

theorem plainComponent_subset (incidence : E → Finset V) (A : Finset V) (Γ : Finset E)
    (e : Γ) : plainComponent incidence A Γ e ⊆ Γ := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
  exact g.property

theorem blockFamily_subset (incidence : E → Finset V) (A : Finset V) (Γ : Finset E)
    {K : Finset E} (hK : K ∈ blockFamily incidence A Γ) : K ⊆ Γ := by
  rw [blockFamily_eq_image] at hK
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hK
  exact plainComponent_subset incidence A Γ e

theorem blockFamily_nonempty (incidence : E → Finset V) (A : Finset V) (Γ : Finset E)
    {K : Finset E} (hK : K ∈ blockFamily incidence A Γ) : K.Nonempty := by
  rw [blockFamily_eq_image] at hK
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hK
  exact ⟨e.val, (mem_plainComponent incidence A Γ e e).mpr (related_refl _ _ _ _)⟩

/-- Every original selected edge belongs to exactly one of the canonical blocks. -/
theorem blockFamily_cover (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) :
    (blockFamily incidence A Γ).biUnion id = Γ := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨K, hK, he⟩ := Finset.mem_biUnion.mp he
    exact blockFamily_subset incidence A Γ hK he
  · intro e he
    refine Finset.mem_biUnion.mpr ⟨plainComponent incidence A Γ ⟨e, he⟩, ?_, ?_⟩
    · rw [blockFamily_eq_image]
      exact Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩
    · exact (mem_plainComponent incidence A Γ _ _).mpr (related_refl _ _ _ _)

/-- Relatedness is preserved by embedding a subgraph into a larger graph. -/
theorem related_mono (incidence : E → Finset V) (A : Finset V)
    {K Γ : Finset E} (hsub : K ⊆ Γ) {e f : K} (h : Related incidence A K e f) :
    Related incidence A Γ ⟨e.val, hsub e.property⟩ ⟨f.val, hsub f.property⟩ := by
  induction h with
  | rel e f h => exact Relation.EqvGen.rel _ _ h
  | refl e => exact Relation.EqvGen.refl _
  | symm e f h ih => exact Relation.EqvGen.symm _ _ ih
  | trans e f g hef hfg ihef ihfg => exact Relation.EqvGen.trans _ _ _ ihef ihfg

/-- Any vertex subset preserved by adjacency is preserved by its equivalence closure. -/
theorem related_preserves_mem (incidence : E → Finset V) (A : Finset V)
    (Γ K : Finset E)
    (hclosed : ∀ e f : Γ, adjacentOutside incidence A Γ e f → (e.val ∈ K ↔ f.val ∈ K))
    {e f : Γ} (h : Related incidence A Γ e f) : e.val ∈ K ↔ f.val ∈ K := by
  induction h with
  | rel e f h => exact hclosed e f h
  | refl e => rfl
  | symm e f h ih => exact ih.symm
  | trans e f g hef hfg ihef ihfg => exact ihef.trans ihfg

/-- Restrict a relation path to an adjacency-closed selected subgraph. -/
theorem related_restrict (incidence : E → Finset V) (A : Finset V)
    (Γ K : Finset E)
    (hclosed : ∀ e f : Γ, adjacentOutside incidence A Γ e f → (e.val ∈ K ↔ f.val ∈ K))
    {e f : Γ} (h : Related incidence A Γ e f) (he : e.val ∈ K) (hf : f.val ∈ K) :
    Related incidence A K ⟨e.val, he⟩ ⟨f.val, hf⟩ := by
  induction h with
  | rel e f h => exact Relation.EqvGen.rel _ _ h
  | refl e => exact Relation.EqvGen.refl _
  | symm e f h ih => exact Relation.EqvGen.symm _ _ (ih hf he)
  | trans e f g hef hfg ihef ihfg =>
    have hfK := (related_preserves_mem incidence A Γ K hclosed hef).mp he
    exact Relation.EqvGen.trans _ _ _ (ihef he hfK) (ihfg hfK hf)

/-- Each canonical component is internally outside-connected. -/
theorem plainComponent_connected (incidence : E → Finset V) (A : Finset V)
    (Γ : Finset E) (e : Γ) : Connected incidence A (plainComponent incidence A Γ e) := by
  let K := plainComponent incidence A Γ e
  have hsub : K ⊆ Γ := plainComponent_subset incidence A Γ e
  have hclosed : ∀ f g : Γ, adjacentOutside incidence A Γ f g → (f.val ∈ K ↔ g.val ∈ K) := by
    intro f g hfg
    change f.val ∈ plainComponent incidence A Γ e ↔ g.val ∈ plainComponent incidence A Γ e
    rw [mem_plainComponent, mem_plainComponent]
    constructor
    · intro hef
      exact related_trans _ _ _ (show Related incidence A Γ e f from hef) (Relation.EqvGen.rel _ _ hfg)
    · intro heg
      exact related_trans _ _ _ (show Related incidence A Γ e g from heg)
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hfg))
  intro f g
  have hef : Related incidence A Γ e ⟨f.val, hsub f.property⟩ :=
    (mem_plainComponent incidence A Γ _ _).mp f.property
  have heg : Related incidence A Γ e ⟨g.val, hsub g.property⟩ :=
    (mem_plainComponent incidence A Γ _ _).mp g.property
  exact related_restrict incidence A Γ K hclosed
    (related_trans _ _ _ (related_symm _ _ _ hef) heg) f.property g.property

/-- Internal connectedness of every member of the canonical partition. -/
theorem blockFamily_connected (incidence : E → Finset V) (A : Finset V) (Γ : Finset E)
    {K : Finset E} (hK : K ∈ blockFamily incidence A Γ) : Connected incidence A K := by
  rw [blockFamily_eq_image] at hK
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hK
  exact plainComponent_connected incidence A Γ e


/-- Canonical blocks that meet at an edge must coincide. -/
theorem plainComponent_eq_of_common (incidence : E → Finset V) (A : Finset V)
    (Γ : Finset E) (e f : Γ) {g : E}
    (hge : g ∈ plainComponent incidence A Γ e) (hgf : g ∈ plainComponent incidence A Γ f) :
    plainComponent incidence A Γ e = plainComponent incidence A Γ f := by
  have hgΓ := plainComponent_subset incidence A Γ e hge
  have heg := (mem_plainComponent incidence A Γ e ⟨g, hgΓ⟩).mp hge
  have hfg := (mem_plainComponent incidence A Γ f ⟨g, hgΓ⟩).mp hgf
  have hef := related_trans incidence A Γ heg (related_symm incidence A Γ hfg)
  exact congrArg (fun K : Finset Γ => K.image Subtype.val)
    (component_eq_of_related incidence A Γ hef)

/-- The ambient-edge canonical family is pairwise edge-disjoint. -/
theorem blockFamily_edge_disjoint (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) :
    (blockFamily incidence A Γ : Set (Finset E)).PairwiseDisjoint id := by
  intro K hK M hM hne
  rw [blockFamily_eq_image] at hK hM
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hM
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  exact hne (plainComponent_eq_of_common incidence A Γ e f hg hg')

/-- The ambient and subtype outside-support representations coincide. -/
theorem outside_plainComponent (incidence : E → Finset V) (A : Finset V)
    (Γ : Finset E) (e : Γ) :
    outside incidence A (plainComponent incidence A Γ e) =
      outsideSupport incidence A Γ (component incidence A Γ e) := by
  ext v
  simp [outside, plainComponent, outsideSupport]

/-- Canonical ambient-edge blocks have disjoint outside supports. -/
theorem blockFamily_outside_disjoint (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) :
    (blockFamily incidence A Γ : Set (Finset E)).PairwiseDisjoint (outside incidence A) := by
  intro K hK M hM hne
  rw [blockFamily_eq_image] at hK hM
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hM
  change Disjoint (outside incidence A (plainComponent incidence A Γ e))
    (outside incidence A (plainComponent incidence A Γ f))
  rw [outside_plainComponent, outside_plainComponent]
  apply outsideSupport_disjoint incidence A Γ e f
  intro h
  exact hne (congrArg (fun K : Finset Γ => K.image Subtype.val) h)

/-- An outside-disjoint selection has no adjacency crossing between its blocks. -/
theorem selection_adjacent_closed (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E))
    (hdisj : (F : Set (Finset E)).PairwiseDisjoint (outside incidence A))
    {K : Finset E} (hK : K ∈ F) (e f : F.biUnion id)
    (hef : adjacentOutside incidence A (F.biUnion id) e f) : e.val ∈ K ↔ f.val ∈ K := by
  obtain ⟨v, hvA, hev, hfv⟩ := hef
  have hstep : ∀ e f : F.biUnion id, v ∈ incidence e → v ∈ incidence f →
      e.val ∈ K → f.val ∈ K := by
    intro e f hev hfv heK
    obtain ⟨M, hM, hfM⟩ := Finset.mem_biUnion.mp f.property
    by_cases hKM : K = M
    · exact hKM.symm ▸ hfM
    · have hvK : v ∈ outside incidence A K :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨e.val, heK, hev⟩, hvA⟩
      have hvM : v ∈ outside incidence A M :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨f.val, hfM, hfv⟩, hvA⟩
      exact False.elim (Finset.disjoint_left.mp (hdisj hK hM hKM) hvK hvM)
  exact ⟨hstep e f hev hfv, hstep f e hfv hev⟩

/-- An internally connected selected block is exactly a canonical component of
the union. Disjointness of outside supports suffices; edge-disjointness is derived. -/
theorem selected_block_eq_component (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E))
    (hdisj : (F : Set (Finset E)).PairwiseDisjoint (outside incidence A))
    {K : Finset E} (hK : K ∈ F) (hconn : Connected incidence A K) (e : K) :
    plainComponent incidence A (F.biUnion id)
      ⟨e.val, Finset.mem_biUnion.mpr ⟨K, hK, e.property⟩⟩ = K := by
  have hsub : K ⊆ F.biUnion id := fun f hf => Finset.mem_biUnion.mpr ⟨K, hK, hf⟩
  ext f
  constructor
  · intro hf
    have hfΓ := plainComponent_subset incidence A (F.biUnion id) _ hf
    have hrel := (mem_plainComponent incidence A (F.biUnion id) _ ⟨f, hfΓ⟩).mp hf
    exact (related_preserves_mem incidence A (F.biUnion id) K
      (selection_adjacent_closed incidence A F hdisj hK) hrel).mp e.property
  · intro hf
    apply (mem_plainComponent incidence A (F.biUnion id) _ ⟨f, hsub hf⟩).mpr
    exact related_mono incidence A hsub (hconn e ⟨f, hf⟩)

/-- Exact reconstruction of an arbitrary valid block selection, without any
assumed decomposition map or uniqueness hypothesis. -/
theorem blockFamily_biUnion (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E)) (hne : ∀ K ∈ F, K.Nonempty)
    (hconn : ∀ K ∈ F, Connected incidence A K)
    (hdisj : (F : Set (Finset E)).PairwiseDisjoint (outside incidence A)) :
    blockFamily incidence A (F.biUnion id) = F := by
  rw [blockFamily_eq_image]
  ext K
  constructor
  · intro hK
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨M, hM, heM⟩ := Finset.mem_biUnion.mp e.property
    have hh := selected_block_eq_component incidence A F hdisj hM (hconn M hM) ⟨e.val, heM⟩
    exact hh.symm ▸ hM
  · intro hK
    obtain ⟨e, he⟩ := hne K hK
    refine Finset.mem_image.mpr ⟨⟨e, Finset.mem_biUnion.mpr ⟨K, hK, he⟩⟩, Finset.mem_univ _, ?_⟩
    exact selected_block_eq_component incidence A F hdisj hK (hconn K hK) ⟨e, he⟩

/-- Two nonempty connected outside-disjoint block selections with the same union
are the same selection. -/
theorem selection_unique (incidence : E → Finset V) (A : Finset V)
    (F G : Finset (Finset E))
    (hFne : ∀ K ∈ F, K.Nonempty) (hGne : ∀ K ∈ G, K.Nonempty)
    (hFc : ∀ K ∈ F, Connected incidence A K) (hGc : ∀ K ∈ G, Connected incidence A K)
    (hFd : (F : Set (Finset E)).PairwiseDisjoint (outside incidence A))
    (hGd : (G : Set (Finset E)).PairwiseDisjoint (outside incidence A))
    (hunion : F.biUnion id = G.biUnion id) : F = G := by
  rw [← blockFamily_biUnion incidence A F hFne hFc hFd,
    ← blockFamily_biUnion incidence A G hGne hGc hGd, hunion]

/-- Edge-disjointness is a consequence of internal connectivity and disjoint
outside supports, including the direct-edge singleton case. -/
theorem selection_edge_disjoint (incidence : E → Finset V) (A : Finset V)
    (F : Finset (Finset E)) (hne : ∀ K ∈ F, K.Nonempty)
    (hconn : ∀ K ∈ F, Connected incidence A K)
    (hdisj : (F : Set (Finset E)).PairwiseDisjoint (outside incidence A)) :
    (F : Set (Finset E)).PairwiseDisjoint id := by
  rw [← blockFamily_biUnion incidence A F hne hconn hdisj]
  exact blockFamily_edge_disjoint incidence A (F.biUnion id)

end SpinGlass.SKBlockPartition
