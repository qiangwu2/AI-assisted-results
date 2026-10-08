import SpinGlass.SKCatalogSelection
import SpinGlass.SKPrimitiveCatalogConnected

/-! # Exact intrinsic characterization of the actual colorful primitive catalog -/
noncomputable section
namespace SpinGlass.SKCatalogMembership
open scoped BigOperators
open SKActualEvaluator SKTraversal SKColorfulCatalog SKCatalogSelection SKBlockPartition
open SKPrimitiveCatalogWalk
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

structure Properties (A : Finset V) (Γ : Finset (Finset V)) : Prop where
  nonempty : Γ.Nonempty
  connected : Connected id A Γ
  uniform : ∀ e ∈ Γ, e.card = 2
  degree : OutsideDegreeTwo id A Γ
  outside_nonempty : (outside id A Γ).Nonempty

theorem properties_of_list (A : Finset V) (Γ : Finset (Finset V)) (l : List V)
    (hl : l ≠ []) (hcard : 0 < Γ.card) (hconn : Connected id A Γ)
    (h2 : ∀ e ∈ Γ, e.card = 2) (hout : outside id A Γ = l.toFinset)
    (hdeg : ∀ v ∈ l, Expansion.degree id Γ v = 2) : Properties A Γ := by
  refine ⟨Finset.card_pos.mp hcard,hconn,h2,?_,?_⟩
  · intro v hv
    rw [hout] at hv
    exact hdeg v (List.mem_toFinset.mp hv)
  · rw [hout, Finset.nonempty_iff_ne_empty]
    simpa using hl

theorem entry_properties {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (tag : Tag A.card) (S : Finset (Fin L)) {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ entry A χ tag S) : Properties A Γ := by
  cases tag with
  | none =>
    simp only [entry] at hΓ
    split at hΓ
    next hS =>
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
      have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
      have ho := lifted_list_outside A χ S hl
      have hlen : 3 ≤ l.length := by simpa [liftedChains_length Subtype.val χ S hl] using hS
      apply properties_of_list A _ l (liftedChains_nonempty Subtype.val χ S hl)
        (by rw [cycleEdges_card hn hlen]; omega)
        (cycleEdges_connected A l ho) (fun e he => cycleEdges_uniform hn hlen he)
        (cycle_outside A χ S hl)
      intro v hv
      simp [cycleEdges_degree hn hlen, hv]
    next hS => simp at hΓ
  | some p =>
    obtain ⟨a,c⟩ := p
    simp only [entry] at hΓ
    split at hΓ
    next hac =>
      split at hΓ
      next hS =>
        obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
        have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
        have ho := lifted_list_outside A χ S hl
        have hroot : ∀ d, branch A d ∉ l := fun d hv => ho _ hv (branch_mem A d)
        have hav : branch A a ≠ branch A c := fun h => hac.ne (branch_injective A h)
        apply properties_of_list A _ l (liftedChains_nonempty Subtype.val χ S hl)
          (by rw [betweenEdges_card hav hn (hroot a) (hroot c)]; omega)
          (betweenEdges_connected A _ _ l ho)
          (fun e he => betweenEdges_uniform hav hn (hroot a) (hroot c) he)
          (path_outside A χ a c S hl)
        intro v hv
        have hva : v ≠ branch A a := fun he => ho _ hv (he ▸ branch_mem A a)
        have hvc : v ≠ branch A c := fun he => ho _ hv (he ▸ branch_mem A c)
        simp [betweenEdges_degree hav hn (hroot a) (hroot c),hv,hva,hvc]
      next hS => simp at hΓ
    next hac =>
      split at hΓ
      next heq =>
        subst c
        split at hΓ
        next hS =>
          obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
          have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
          have ho := lifted_list_outside A χ S hl
          have hr : branch A a ∉ l := fun hv => ho _ hv (branch_mem A a)
          have hlen : 2 ≤ l.length := by simpa [liftedChains_length Subtype.val χ S hl] using hS
          apply properties_of_list A _ l (liftedChains_nonempty Subtype.val χ S hl)
            (by rw [rootedEdges_card hn hr hlen]; omega)
            (rootedEdges_connected A _ l ho) (fun e he => rootedEdges_uniform hn hr hlen he)
            (return_outside A χ a S hl)
          intro v hv
          simp [rootedEdges_degree hn hr hlen,hv]
        next hS => simp at hΓ
      next heq => simp at hΓ

theorem catalog_properties {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    {Γ : Finset (Finset V)} (hΓ : Γ ∈ catalog A χ) : Properties A Γ := by
  obtain ⟨p,hp,hΓ⟩ := Finset.mem_biUnion.mp hΓ
  exact entry_properties A χ p.1 p.2 hΓ

theorem lift_outside_list (A : Finset V) (l : List V) (ho : ∀ v ∈ l, v ∉ A) :
    ∃ q : List (Outside A), q.map Subtype.val = l := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons v l ih =>
    obtain ⟨q,hq⟩ := ih (fun w hw => ho w (List.mem_cons_of_mem v hw))
    exact ⟨⟨v,ho v (by simp)⟩::q,by simp [hq]⟩

/-- Every colorful nonempty outside list is present in the literal table catalog. -/
theorem lifted_of_outside_colorful {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (l : List V) (hn : l.Nodup) (hne : l ≠ []) (ho : ∀ v ∈ l, v ∉ A)
    (hc : Set.InjOn (totalColor A χ hL) l.toFinset) :
    l ∈ liftedChains Subtype.val χ (l.toFinset.image (totalColor A χ hL)) := by
  obtain ⟨q,hq⟩ := lift_outside_list A l ho
  have he : q.map χ = l.map (totalColor A χ hL) := by
    rw [← hq, List.map_map]
    simp [Function.comp_def]
  refine Finset.mem_image.mpr ⟨q,?_,hq⟩
  apply (SKPrimitiveTables.mem_allChains χ _ q).mpr
  refine ⟨?_,?_,?_⟩
  · intro hz; subst q; simp at hq; exact hne hq
  · rw [he]
    exact (List.nodup_map_iff_inj_on hn).mpr
      (fun v hv w hw => hc (by simpa using hv) (by simpa using hw))
  · rw [he]
    ext c
    simp

theorem mem_catalog_of_entry {L : ℕ} (A : Finset V) (χ : Outside A → Fin L)
    (tag : Tag A.card) (S : Finset (Fin L)) {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ entry A χ tag S) : Γ ∈ catalog A χ :=
  Finset.mem_biUnion.mpr ⟨(tag,S),Finset.mem_univ _,hΓ⟩

theorem betweenEdges_reverse_swap (a b : V) (l : List V) :
    betweenEdges b a l.reverse = betweenEdges a b l := by
  unfold betweenEdges
  rw [← pathEdges_reverse]
  simp [List.reverse_cons, List.reverse_append]

/-- Completeness follows from the derived primitive classification, not an
assumption that graph blocks occur among the dynamic-programming states. -/
theorem mem_catalog_of_properties {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (Γ : Finset (Finset V)) (hΓ : Properties A Γ)
    (hc : SKGraphMonomial.Colorful id A (totalColor A χ hL) Γ) : Γ ∈ catalog A χ := by
  have hclass := primitive_classification A Γ hΓ.nonempty hΓ.connected hΓ.uniform hΓ.degree
  rcases hclass with hdir | hpath | hreturn | hcycle
  · obtain ⟨a,ha,b,hb,hab,rfl⟩ := hdir
    obtain ⟨v,hv⟩ := hΓ.outside_nonempty
    obtain ⟨hvU,hvA⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hvU
    have heq : e = {a,b} := Finset.mem_singleton.mp he
    simp only [id_eq,heq,Finset.mem_insert,Finset.mem_singleton] at hve
    rcases hve with rfl | rfl <;> contradiction
  · obtain ⟨a,ha,c,hcA,hac,l,hn,hlen,ho,hout,he⟩ := hpath
    have hcolor : Set.InjOn (totalColor A χ hL) l.toFinset := by
      rw [hout]; exact hc
    have hl := lifted_of_outside_colorful A χ hL l hn
      (by intro hz; simp [hz] at hlen) ho hcolor
    let S := l.toFinset.image (totalColor A χ hL)
    have hS : 1 ≤ S.card := by rw [← liftedChains_length Subtype.val χ S hl]; exact hlen
    obtain ⟨a,rfl⟩ := (branch_range A a).mp ha
    obtain ⟨c,rfl⟩ := (branch_range A c).mp hcA
    by_cases hlt : a < c
    · apply mem_catalog_of_entry A χ (some (a,c)) S
      simp only [entry,if_pos hlt,if_pos hS]
      exact Finset.mem_image.mpr ⟨l,hl,he.symm⟩
    · have hca : c < a := by
        have hne : a ≠ c := fun heq => hac (congrArg (branch A) heq)
        omega
      apply mem_catalog_of_entry A χ (some (c,a)) S
      simp only [entry,if_pos hca,if_pos hS]
      refine Finset.mem_image.mpr ⟨l.reverse,?_,?_⟩
      · exact liftedChains_closed Subtype.val (outside_injective A) χ S l hl l.reverse (List.reverse_perm l)
      · exact (betweenEdges_reverse_swap _ _ _).trans he.symm
  · obtain ⟨a,ha,l,hn,hlen,ho,hout,he⟩ := hreturn
    have hcolor : Set.InjOn (totalColor A χ hL) l.toFinset := by rw [hout]; exact hc
    have hl := lifted_of_outside_colorful A χ hL l hn
      (by intro hz; simp [hz] at hlen) ho hcolor
    let S := l.toFinset.image (totalColor A χ hL)
    have hS : 2 ≤ S.card := by rw [← liftedChains_length Subtype.val χ S hl]; exact hlen
    obtain ⟨a,rfl⟩ := (branch_range A a).mp ha
    apply mem_catalog_of_entry A χ (some (a,a)) S
    simp only [entry,lt_self_iff_false,if_false,if_pos rfl,if_pos hS]
    exact Finset.mem_image.mpr ⟨l,hl,he.symm⟩
  · obtain ⟨l,hn,hlen,ho,hout,he⟩ := hcycle
    have hcolor : Set.InjOn (totalColor A χ hL) l.toFinset := by rw [hout]; exact hc
    have hl := lifted_of_outside_colorful A χ hL l hn
      (by intro hz; simp [hz] at hlen) ho hcolor
    let S := l.toFinset.image (totalColor A χ hL)
    have hS : 3 ≤ S.card := by rw [← liftedChains_length Subtype.val χ S hl]; exact hlen
    apply mem_catalog_of_entry A χ none S
    simp only [entry,if_pos hS]
    exact Finset.mem_image.mpr ⟨l,hl,he.symm⟩

/-- The actual finite table catalog is exactly the intrinsically specified
non-direct primitive family. -/
theorem catalog_iff {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (Γ : Finset (Finset V)) : Γ ∈ catalog A χ ↔
      Properties A Γ ∧ SKGraphMonomial.Colorful id A (totalColor A χ hL) Γ :=
  ⟨fun h => ⟨catalog_properties A χ h,catalog_colorful A χ hL h⟩,
    fun h => mem_catalog_of_properties A χ hL Γ h.1 h.2⟩

end SpinGlass.SKCatalogMembership
