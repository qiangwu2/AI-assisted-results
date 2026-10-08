import SpinGlass.SKColorfulCatalog

/-! # Unique indexing and disjoint union of the finite colorful catalogs -/
noncomputable section
namespace SpinGlass.SKCatalogSelection
open scoped BigOperators
open SKActualEvaluator SKColorfulCatalog SKTraversal
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No branch endpoint, one repeated endpoint, or two ordered distinct endpoints. -/
abbrev Tag (b : ℕ) := Option (Fin b × Fin b)

def ValidTag {b : ℕ} : Tag b → Prop
  | none => True
  | some p => p.1 ≤ p.2

def tagVertices (A : Finset V) : Tag A.card → Finset V
  | none => ∅
  | some p => {branch A p.1, branch A p.2}

/-- One literal primitive catalog, with the simple-path/cycle size restrictions. -/
def entry {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (tag : Tag A.card) (S : Finset (Fin L)) : Finset (Finset (Finset V)) :=
  match tag with
  | none => if 3 ≤ S.card then cycleCatalog A χ S else ∅
  | some (a,c) =>
      if a < c then if 1 ≤ S.card then pathCatalog A χ a c S else ∅
      else if a = c then if 2 ≤ S.card then returnCatalog A χ a S else ∅ else ∅

/-- The three primitive cases have distinct graph signatures, with the exact colors. -/
theorem entry_signature {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (tag : Tag A.card) (S : Finset (Fin L)) {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ entry A χ tag S) :
    ValidTag tag ∧ SKGraphMonomial.colors id A (totalColor A χ hL) Γ = S ∧
      branchSupport A Γ = tagVertices A tag ∧
      SKGraphMonomial.Colorful id A (totalColor A χ hL) Γ := by
  cases tag with
  | none =>
    simp only [entry] at hΓ
    split at hΓ
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hΓ
      refine ⟨trivial, ?_, cycle_branchSupport A χ S hl, ?_⟩
      · rw [SKGraphMonomial.colors, cycle_outside A χ S hl]
        exact lifted_list_colors A χ hL S hl
      · rw [SKGraphMonomial.Colorful, cycle_outside A χ S hl]
        exact lifted_list_colorful A χ hL S hl
    · simp at hΓ
  | some p =>
    rcases p with ⟨a,c⟩
    simp only [entry] at hΓ
    split at hΓ
    next hac =>
      split at hΓ
      next hs =>
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hΓ
        refine ⟨le_of_lt hac, ?_, path_branchSupport A χ a c S hl, ?_⟩
        · rw [SKGraphMonomial.colors, path_outside A χ a c S hl]
          exact lifted_list_colors A χ hL S hl
        · rw [SKGraphMonomial.Colorful, path_outside A χ a c S hl]
          exact lifted_list_colorful A χ hL S hl
      next hs => simp at hΓ
    next hac =>
      split at hΓ
      next heq =>
        subst c
        split at hΓ
        next hs =>
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hΓ
          refine ⟨le_refl _, ?_, ?_, ?_⟩
          · rw [SKGraphMonomial.colors, return_outside A χ a S hl]
            exact lifted_list_colors A χ hL S hl
          · simpa [tagVertices] using return_branchSupport A χ a S hl
          · rw [SKGraphMonomial.Colorful, return_outside A χ a S hl]
            exact lifted_list_colorful A χ hL S hl
        next hs => simp at hΓ
      next heq => simp at hΓ

/-- Ordered endpoint labels are recovered from the actual branch support. -/
theorem tagVertices_injective (A : Finset V) {t u : Tag A.card}
    (ht : ValidTag t) (hu : ValidTag u) (h : tagVertices A t = tagVertices A u) : t = u := by
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some p =>
      have hm : branch A p.1 ∈ tagVertices A (some p) := by simp [tagVertices]
      rw [← h] at hm
      simp [tagVertices] at hm
  | some p =>
    cases u with
    | none =>
      have hm : branch A p.1 ∈ tagVertices A (some p) := by simp [tagVertices]
      rw [h] at hm
      simp [tagVertices] at hm
    | some q =>
      have hs : ({branch A p.1, branch A p.2} : Set V) =
          {branch A q.1, branch A q.2} := by
        simpa [tagVertices] using congrArg (fun s : Finset V => (s : Set V)) h
      rcases Set.pair_eq_pair_iff.mp hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have hpq : p = q := Prod.ext (branch_injective A h1) (branch_injective A h2)
        exact congrArg some hpq
      · have h1' := branch_injective A h1
        have h2' := branch_injective A h2
        have hp : p.1 = p.2 := le_antisymm ht (by simpa [ValidTag, h1',h2'] using hu)
        have hpq : p = q := Prod.ext (hp.trans h2') (hp.symm.trans h1')
        exact congrArg some hpq

/-- An actual primitive graph has exactly one catalog tag and color subset. -/
theorem entry_key_unique {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    {t u : Tag A.card} {S T : Finset (Fin L)} {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ entry A χ t S) (hΓ' : Γ ∈ entry A χ u T) : t = u ∧ S = T := by
  obtain ⟨ht, hS, hv, hc⟩ := entry_signature A χ hL t S hΓ
  obtain ⟨hu, hT, hw, hc'⟩ := entry_signature A χ hL u T hΓ'
  exact ⟨tagVertices_injective A ht hu (hv.symm.trans hw), hS.symm.trans hT⟩

/-- Complete finite primitive catalog supplied by the actual colorful tables. -/
def catalog {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) : Finset (Finset (Finset V)) :=
  Finset.univ.biUnion (fun p : Tag A.card × Finset (Fin L) => entry A χ p.1 p.2)

/-- Every graph in the complete catalog is internally outside-colorful. -/
theorem catalog_colorful {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    {Γ : Finset (Finset V)} (hΓ : Γ ∈ catalog A χ) :
    SKGraphMonomial.Colorful id A (totalColor A χ hL) Γ := by
  obtain ⟨p, hp, hΓ⟩ := Finset.mem_biUnion.mp hΓ
  exact (entry_signature A χ hL p.1 p.2 hΓ).2.2.2

/-- Summing per recurrence state neither omits nor duplicates a primitive graph. -/
theorem sum_catalog {L : ℕ} {R : Type*} [AddCommMonoid R]
    (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset (Finset V) → R) :
    (∑ Γ ∈ catalog A χ, f Γ) =
      ∑ p : Tag A.card × Finset (Fin L), ∑ Γ ∈ entry A χ p.1 p.2, f Γ := by
  rw [catalog, Finset.sum_biUnion]
  intro p hp q hq hpq
  apply Finset.disjoint_left.mpr
  intro Γ hΓ hΓ'
  obtain ⟨he1,he2⟩ := entry_key_unique A χ hL hΓ hΓ'
  exact hpq (Prod.ext he1 he2)

end SpinGlass.SKCatalogSelection
