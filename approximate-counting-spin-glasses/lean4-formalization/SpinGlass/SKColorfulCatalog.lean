import SpinGlass.SKActualEvaluator
import SpinGlass.SKTraversalPrimitives

/-! # Concrete finite catalogs of colorful primitive graphs -/
noncomputable section
namespace SpinGlass.SKColorfulCatalog
open scoped BigOperators
open SKActualEvaluator SKTraversal
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Outside cycles represented by the actual chain table. -/
def cycleCatalog {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (S : Finset (Fin L)) :
    Finset (Finset (Finset V)) := (liftedChains Subtype.val χ S).image cycleEdges

/-- Cycles visiting exactly the specified single branch label. -/
def returnCatalog {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (a : Fin A.card) (S : Finset (Fin L)) : Finset (Finset (Finset V)) :=
  (liftedChains Subtype.val χ S).image (rootedEdges (branch A a))

/-- Paths whose distinct branch endpoints are fixed by their labels. -/
def pathCatalog {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (a c : Fin A.card) (S : Finset (Fin L)) : Finset (Finset (Finset V)) :=
  (liftedChains Subtype.val χ S).image (betweenEdges (branch A a) (branch A c))

/-- An ambient list emitted by the outside table contains only outside vertices. -/
theorem lifted_list_outside {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (S : Finset (Fin L)) {l : List V} (hl : l ∈ liftedChains Subtype.val χ S) :
    ∀ v ∈ l, v ∉ A := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hl
  intro v hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  exact u.property

/-- Outside table lists retain exactly their stated color subset after ambient lifting. -/
theorem lifted_list_colors {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (S : Finset (Fin L)) {l : List V} (hl : l ∈ liftedChains Subtype.val χ S) :
    l.toFinset.image (totalColor A χ hL) = S := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hl
  have hS := (SKPrimitiveTables.mem_allChains χ S q).mp hq |>.2.2
  rw [← hS]
  ext c
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, hc⟩
    exact ⟨u, hu, by simpa using hc⟩
  · rintro ⟨u, hu, hc⟩
    exact ⟨u.val, ⟨u, hu, rfl⟩, by simpa using hc⟩

/-- No ambient outside vertex lists share a color internally. -/
theorem lifted_list_colorful {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (S : Finset (Fin L)) {l : List V} (hl : l ∈ liftedChains Subtype.val χ S) :
    Set.InjOn (totalColor A χ hL) l.toFinset := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hl
  have hn := (SKPrimitiveTables.mem_allChains χ S q).mp hq |>.2.1
  have hqn := SKTraversal.allChains_nodup χ S hq
  have hinj := (List.nodup_map_iff_inj_on hqn).mp hn
  intro v hv u hu heq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
  have hxy : χ x = χ y := by simpa using heq
  exact congrArg Subtype.val (hinj x hx y hy hxy)

private theorem support_sdiff_eq (A B : Finset V) (l : List V)
    (hB : B ⊆ A) (hl : ∀ v ∈ l, v ∉ A) : (B ∪ l.toFinset) \ A = l.toFinset := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset]
  constructor
  · rintro ⟨hv | hv, ha⟩
    · exact False.elim (ha (hB hv))
    · exact hv
  · intro hv
    exact ⟨Or.inr hv, hl v hv⟩

/-- Every primitive type has precisely its interior list as outside support. -/
theorem cycle_outside {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (S : Finset (Fin L)) {l : List V} (hl : l ∈ liftedChains Subtype.val χ S) :
    SKGraphMonomial.outside id A (cycleEdges l) = l.toFinset := by
  change Hypergraph.support (cycleEdges l) \ A = _
  rw [cycleEdges_support]
  exact support_sdiff_eq A ∅ l (by simp) (lifted_list_outside A χ S hl)

theorem return_outside {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (a : Fin A.card) (S : Finset (Fin L)) {l : List V}
    (hl : l ∈ liftedChains Subtype.val χ S) :
    SKGraphMonomial.outside id A (rootedEdges (branch A a) l) = l.toFinset := by
  change Hypergraph.support (rootedEdges (branch A a) l) \ A = _
  rw [rootedEdges_support]
  exact support_sdiff_eq A {branch A a} l (by simpa using branch_mem A a)
    (lifted_list_outside A χ S hl)

theorem path_outside {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (a c : Fin A.card) (S : Finset (Fin L)) {l : List V}
    (hl : l ∈ liftedChains Subtype.val χ S) :
    SKGraphMonomial.outside id A (betweenEdges (branch A a) (branch A c) l) = l.toFinset := by
  change Hypergraph.support (betweenEdges (branch A a) (branch A c) l) \ A = _
  rw [betweenEdges_support]
  have hB : ({branch A a, branch A c} : Finset V) ⊆ A := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> apply branch_mem
  simpa using support_sdiff_eq A {branch A a, branch A c} l hB (lifted_list_outside A χ S hl)

/-- Branch vertices appearing in a primitive, used to distinguish the primitive catalogs. -/
def branchSupport (A : Finset V) (Γ : Finset (Finset V)) : Finset V :=
  Hypergraph.support Γ ∩ A

private theorem support_inter_eq (A B : Finset V) (l : List V)
    (hB : B ⊆ A) (hl : ∀ v ∈ l, v ∉ A) : (B ∪ l.toFinset) ∩ A = B := by
  ext v
  simp only [Finset.mem_inter, Finset.mem_union, List.mem_toFinset]
  constructor
  · rintro ⟨hv | hv, ha⟩
    · exact hv
    · exact False.elim (hl v hv ha)
  · intro hv
    exact ⟨Or.inl hv, hB hv⟩

theorem cycle_branchSupport {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (S : Finset (Fin L)) {l : List V} (hl : l ∈ liftedChains Subtype.val χ S) :
    branchSupport A (cycleEdges l) = ∅ := by
  unfold branchSupport
  rw [cycleEdges_support]
  exact support_inter_eq A ∅ l (by simp) (lifted_list_outside A χ S hl)

theorem return_branchSupport {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (a : Fin A.card) (S : Finset (Fin L)) {l : List V}
    (hl : l ∈ liftedChains Subtype.val χ S) :
    branchSupport A (rootedEdges (branch A a) l) = {branch A a} := by
  unfold branchSupport
  rw [rootedEdges_support]
  exact support_inter_eq A {branch A a} l (by simpa using branch_mem A a)
    (lifted_list_outside A χ S hl)

theorem path_branchSupport {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (a c : Fin A.card) (S : Finset (Fin L)) {l : List V}
    (hl : l ∈ liftedChains Subtype.val χ S) :
    branchSupport A (betweenEdges (branch A a) (branch A c) l) = {branch A a, branch A c} := by
  unfold branchSupport
  rw [betweenEdges_support]
  have hB : ({branch A a, branch A c} : Finset V) ⊆ A := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> apply branch_mem
  simpa using support_inter_eq A {branch A a, branch A c} l hB (lifted_list_outside A χ S hl)

end SpinGlass.SKColorfulCatalog
