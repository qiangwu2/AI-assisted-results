import SpinGlass.SKBranchingPairings
import SpinGlass.Support

/-!
# Simple graph realizations inject into distinguished-stub pairings

The objects are actual finite families of two-element vertex sets. A realization
with prescribed degrees, together with an independent labeling of the stubs at
each vertex, determines a fixed-point-free partner permutation. The map is
injective: the permutation recovers both every graph edge and every stub label.
-/
noncomputable section
namespace SpinGlass.SKBranching
open scoped BigOperators Nat
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual simple graphs with the specified complete degree sequence. -/
abbrev Realization (d : V → ℕ) :=
  {Γ : Finset (Finset V) // (∀ e ∈ Γ, e.card = 2) ∧ ∀ v, SpinGlass.Hypergraph.degree Γ v = d v}

instance (d : V → ℕ) : Fintype (Realization d) := by
  classical
  unfold Realization
  infer_instance

/-- The distinguished stubs attached to their vertices. -/
abbrev Stubs (d : V → ℕ) := (v : V) × Fin (d v)


/-- The actual incident edges at a vertex in a selected graph. -/
abbrev Incident (Γ : Finset (Finset V)) (v : V) := {e : Finset V // e ∈ Γ ∧ v ∈ e}

instance (Γ : Finset (Finset V)) (v : V) : Fintype (Incident Γ v) := by
  classical
  unfold Incident
  infer_instance

/-- A labeling bijects each vertex's distinguished stubs with its incident edges. -/
abbrev Labeling {d : V → ℕ} (Γ : Realization d) := ∀ v, Fin (d v) ≃ Incident Γ.val v


/-- Actual incidences, used to define the canonical edge-partner permutation. -/
abbrev Incidence (Γ : Finset (Finset V)) := {ve : V × Finset V // ve.2 ∈ Γ ∧ ve.1 ∈ ve.2}

instance (Γ : Finset (Finset V)) : Fintype (Incidence Γ) := by
  classical
  unfold Incidence
  infer_instance

private theorem exists_other {e : Finset V} (he : e.card = 2) {v : V} (hv : v ∈ e) :
    ∃ w, w ∈ e ∧ w ≠ v := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨y, by simp, hxy.symm⟩
  · exact ⟨x, by simp, hxy⟩

/-- The unique opposite endpoint of an actual two-element edge. -/
def otherEndpoint (e : Finset V) (he : e.card = 2) (v : V) (hv : v ∈ e) : V :=
  Classical.choose (exists_other he hv)

private theorem otherEndpoint_mem (e : Finset V) (he : e.card = 2) (v : V) (hv : v ∈ e) :
    otherEndpoint e he v hv ∈ e := (Classical.choose_spec (exists_other he hv)).1

private theorem otherEndpoint_ne (e : Finset V) (he : e.card = 2) (v : V) (hv : v ∈ e) :
    otherEndpoint e he v hv ≠ v := (Classical.choose_spec (exists_other he hv)).2

/-- Both endpoints recover the exact original edge. -/
theorem edge_eq_endpoints (e : Finset V) (he : e.card = 2) (v : V) (hv : v ∈ e) :
    e = {v, otherEndpoint e he v hv} := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    have hx' : x = v ∨ x = otherEndpoint e he v hv := by
      by_contra h
      push Not at h
      have hsub : {v, otherEndpoint e he v hv, x} ⊆ e := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact hv
        · exact otherEndpoint_mem e he v hv
        · exact hx
      have hc := Finset.card_le_card hsub
      have hne := otherEndpoint_ne e he v hv
      simp [hne, hne.symm, h.1, h.1.symm, h.2, h.2.symm, he] at hc
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx'
  · rw [Finset.card_insert_of_notMem (by simpa using (otherEndpoint_ne e he v hv).symm)]
    simp [he]

private theorem otherEndpoint_involutive (e : Finset V) (he : e.card = 2)
    (v : V) (hv : v ∈ e) :
    otherEndpoint e he (otherEndpoint e he v hv) (otherEndpoint_mem e he v hv) = v := by
  have hm := otherEndpoint_mem e he (otherEndpoint e he v hv) (otherEndpoint_mem e he v hv)
  have hm' := (edge_eq_endpoints e he v hv).subset hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
  exact hm'.resolve_right (otherEndpoint_ne e he _ _)

/-- Partner along the same original graph edge. -/
def incidencePartner {d : V → ℕ} (Γ : Realization d) (h : Incidence Γ.val) : Incidence Γ.val :=
  ⟨(otherEndpoint h.val.2 (Γ.property.1 _ h.property.1) h.val.1 h.property.2, h.val.2),
    h.property.1, otherEndpoint_mem h.val.2 (Γ.property.1 _ h.property.1) h.val.1 h.property.2⟩

theorem incidencePartner_involutive {d : V → ℕ} (Γ : Realization d) :
    Function.Involutive (incidencePartner Γ) := by
  intro h
  apply Subtype.ext
  apply Prod.ext
  · change otherEndpoint h.val.2 (Γ.property.1 _ h.property.1)
      (otherEndpoint h.val.2 (Γ.property.1 _ h.property.1) h.val.1 h.property.2)
      (otherEndpoint_mem h.val.2 (Γ.property.1 _ h.property.1) h.val.1 h.property.2) = h.val.1
    exact otherEndpoint_involutive h.val.2 (Γ.property.1 _ h.property.1) h.val.1 h.property.2
  · rfl

theorem incidencePartner_fixedPointFree {d : V → ℕ} (Γ : Realization d)
    (h : Incidence Γ.val) : incidencePartner Γ h ≠ h := by
  intro heq
  apply otherEndpoint_ne h.val.2 (Γ.property.1 _ h.property.1) h.val.1 h.property.2
  exact congrArg (fun t : Incidence Γ.val => t.val.1) heq

/-- The graph's canonical edge-partner equivalence on actual incidences. -/
def incidencePairing {d : V → ℕ} (Γ : Realization d) : Equiv.Perm (Incidence Γ.val) :=
  (incidencePartner_involutive Γ).toPerm

/-- Stub labels give a genuine equivalence with actual graph incidences. -/
def labelingEquiv {d : V → ℕ} (Γ : Realization d) (L : Labeling Γ) : Stubs d ≃ Incidence Γ.val where
  toFun h := ⟨(h.fst, (L h.fst h.snd).val), (L h.fst h.snd).property⟩
  invFun h := ⟨h.val.1, (L h.val.1).symm ⟨h.val.2, h.property⟩⟩
  left_inv h := by cases h; simp
  right_inv h := by apply Subtype.ext; simp

/-- The actual distinguished-stub pairing induced by a labeled simple graph. -/
def realizationPairing {d : V → ℕ} (Γ : Realization d) (L : Labeling Γ) : Pairing (Stubs d) := by
  let e := labelingEquiv Γ L
  let σ : Equiv.Perm (Stubs d) := e.trans ((incidencePairing Γ).trans e.symm)
  refine ⟨σ, ?_, ?_⟩
  · apply Equiv.ext
    intro h
    change e.symm (incidencePartner Γ (e (e.symm (incidencePartner Γ (e h))))) = h
    rw [e.apply_symm_apply, incidencePartner_involutive, e.symm_apply_apply]
  · intro h heq
    apply incidencePartner_fixedPointFree Γ (e h)
    have hh := congrArg e heq
    change e (e.symm (incidencePartner Γ (e h))) = e h at hh
    rw [e.apply_symm_apply] at hh
    exact hh


/-- A labeled edge is recovered from the vertices of its two paired stubs. -/
theorem labeling_edge_eq (d : V → ℕ) (Γ : Realization d) (L : Labeling Γ) (h : Stubs d) :
    (L h.fst h.snd).val = {h.fst, ((realizationPairing Γ L).val h).fst} := by
  change (L h.fst h.snd).val = {h.fst,
    otherEndpoint (L h.fst h.snd).val (Γ.property.1 _ (L h.fst h.snd).property.1)
      h.fst (L h.fst h.snd).property.2}
  exact edge_eq_endpoints _ _ _ _

/-- Recover the simple edge family from a distinguished-stub partner permutation. -/
def graphOfPairing (d : V → ℕ) (σ : Pairing (Stubs d)) : Finset (Finset V) :=
  Finset.univ.image (fun h : Stubs d => {h.fst, (σ.val h).fst})

/-- Pairing reconstruction recovers every original graph edge, exactly. -/
theorem graphOf_realizationPairing (d : V → ℕ) (Γ : Realization d) (L : Labeling Γ) :
    graphOfPairing d (realizationPairing Γ L) = Γ.val := by
  ext e
  constructor
  · intro he
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp he
    rw [← labeling_edge_eq]
    exact (L h.fst h.snd).property.1
  · intro he
    have hnonempty : e.Nonempty := Finset.card_pos.mp (by rw [Γ.property.1 e he]; omega)
    obtain ⟨v, hv⟩ := hnonempty
    let h : Stubs d := ⟨v, (L v).symm ⟨e, he, hv⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨h, Finset.mem_univ _, ?_⟩
    rw [← labeling_edge_eq]
    simp [h]

/-- No graph or labeling multiplicity is lost in the stub-pairing encoding. -/
theorem realizationPairing_injective (d : V → ℕ) :
    Function.Injective (fun p : (Γ : Realization d) × Labeling Γ => realizationPairing p.fst p.snd) := by
  rintro ⟨Γ, L⟩ ⟨Δ, M⟩ h
  have hΓ : Γ = Δ := by
    apply Subtype.ext
    rw [← graphOf_realizationPairing d Γ L, ← graphOf_realizationPairing d Δ M]
    exact congrArg (graphOfPairing d) h
  subst Δ
  have hL : L = M := by
    funext v
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rw [labeling_edge_eq d Γ L ⟨v, i⟩, labeling_edge_eq d Γ M ⟨v, i⟩]
    congr 2
    exact congrArg (fun σ : Pairing (Stubs d) => (σ.val ⟨v, i⟩).fst) h
  subst M
  rfl

/-- The incident-edge type has exactly the prescribed degree. -/
theorem card_incident {d : V → ℕ} (Γ : Realization d) (v : V) :
    Fintype.card (Incident Γ.val v) = d v := by
  have h : Fintype.card (Incident Γ.val v) = (Γ.val.filter (fun e => v ∈ e)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h.trans (Γ.property.2 v)

/-- There are exactly ∏v dᵥ! independent distinguished-stub labelings of each graph. -/
theorem card_labeling {d : V → ℕ} (Γ : Realization d) :
    Fintype.card (Labeling Γ) = ∏ v, (d v).factorial := by
  classical
  unfold Labeling
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro v hv
  have e : Fin (d v) ≃ Incident Γ.val v := Fintype.equivOfCardEq (by simp [card_incident])
  simpa only [Fintype.card_fin] using Fintype.card_equiv e

/-- The degree-sequence counting inequality used in Lemma 6.1, with the
multiplicity and pairing count both proved for actual finite simple graphs. -/
theorem degree_realization_count_mul_factorials (d : V → ℕ) {k : ℕ}
    (hsum : ∑ v, d v = 2 * k) :
    Fintype.card (Realization d) * (∏ v, (d v).factorial) ≤ (2 * k - 1)‼ := by
  have hH : Fintype.card (Stubs d) = 2 * k := by
    unfold Stubs
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using hsum
  calc
    _ = Fintype.card ((Γ : Realization d) × Labeling Γ) := by
      rw [Fintype.card_sigma]
      simp only [card_labeling, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ ≤ Fintype.card (Pairing (Stubs d)) := Fintype.card_le_of_injective _ (realizationPairing_injective d)
    _ ≤ _ := card_pairings_le hH

end SpinGlass.SKBranching

