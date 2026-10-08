import SpinGlass.SKComponents
import SpinGlass.SKGraphShapes

/-!
# Path/cycle classification for the actual outside induced graph

The input is the selected finite edge family. Adjacency is defined by membership
of the actual unordered pair; degree bounds are proved by injection into the
actual incident-edge set. Every outside connected component is then classified
using the longest-path theorem.
-/

noncomputable section

namespace SpinGlass.SKOutsideClassification

open SimpleGraph SKComponents

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Interpret the selected two-element edges as an ordinary simple graph. -/
def graph (Γ : Finset (Finset V)) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ({v, w} : Finset V) ∈ Γ
  symm := ⟨by intro v w h; exact ⟨h.1.symm, by simpa [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- Every graph neighbor yields a distinct actual selected incident edge. -/
theorem neighbor_card_le_degree (Γ : Finset (Finset V)) (v : V) :
    ((graph Γ).neighborSet v).ncard ≤ Expansion.degree id Γ v := by
  classical
  have h := Set.ncard_le_ncard_of_injOn (fun w : V => ({v, w} : Finset V))
    (s := (graph Γ).neighborSet v) (t := (Γ.filter (fun e => v ∈ e) : Set (Finset V)))
    (fun w hw => Finset.mem_filter.mpr ⟨hw.2, by simp⟩) ?_
  · simpa only [Set.ncard_coe_finset, Expansion.degree, id_eq] using h
  · intro w hw w' hw' heq
    dsimp at heq
    have hm : w ∈ ({v, w'} : Finset V) := by rw [← heq]; simp
    have hor : w = v ∨ w = w' := by simpa using hm
    rcases hor with h | h
    · exact False.elim (hw.1 h.symm)
    · exact h

/-- For genuine two-element edges, ordinary neighbor count equals hypergraph degree. -/
theorem neighbor_card_eq_degree (Γ : Finset (Finset V))
    (h2 : ∀ e ∈ Γ, e.card = 2) (v : V) :
    ((graph Γ).neighborSet v).ncard = Expansion.degree id Γ v := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  unfold Expansion.degree
  apply Finset.card_bij (fun w _ => ({v, w} : Finset V))
  · intro w hw
    have ha : (graph Γ).Adj v w := by simpa using hw
    exact Finset.mem_filter.mpr ⟨ha.2, by simp⟩
  · intro w hw w' hw' heq
    have ha : (graph Γ).Adj v w := by simpa using hw
    have hm : w ∈ ({v, w'} : Finset V) := by rw [← heq]; simp
    have hor : w = v ∨ w = w' := by simpa using hm
    exact hor.elim (fun h => False.elim (ha.1 h.symm)) id
  · intro e he
    obtain ⟨heΓ, hev⟩ := Finset.mem_filter.mp he
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (h2 e heΓ)
    have hor : v = a ∨ v = b := by simpa using hev
    rcases hor with rfl | rfl
    · refine ⟨b, ?_, rfl⟩
      change b ∈ ((graph Γ).neighborSet v).toFinset
      simpa [graph] using And.intro hab heΓ
    · refine ⟨a, ?_, Finset.pair_comm _ _⟩
      change a ∈ ((graph Γ).neighborSet v).toFinset
      simp only [Set.mem_toFinset, mem_neighborSet, graph]
      exact ⟨hab.symm, by simpa [Finset.pair_comm] using heΓ⟩

/-- Inducing a graph on a vertex subset cannot increase its neighbor count. -/
theorem induced_neighbor_card_le (G : SimpleGraph V) (S : Set V) (v : S) :
    ((G.induce S).neighborSet v).ncard ≤ (G.neighborSet v.val).ncard := by
  apply Set.ncard_le_ncard_of_injOn (fun w : S => w.val)
  · intro w hw
    exact hw
  · intro w hw w' hw' heq
    exact Subtype.ext heq

/-- The outside graph is the literal induced graph on nonbranch vertices. -/
def outsideGraph (Γ : Finset (Finset V)) : SimpleGraph {v : V // v ∉ branchVertices id Γ} :=
  (graph Γ).induce {v : V | v ∉ branchVertices id Γ}

/-- Parity and the definition of branching force maximum outside degree two. -/
theorem outside_neighbor_card_le_two (Γ : Finset (Finset V))
    (heven : Expansion.IsEven id Γ) (v : {v : V // v ∉ branchVertices id Γ}) :
    ((outsideGraph Γ).neighborSet v).ncard ≤ 2 := by
  have hlow : Expansion.degree id Γ v.val < 4 := by
    simpa [branchVertices] using v.property
  have hpar := Nat.even_iff.mp (heven v.val)
  have hdegree : Expansion.degree id Γ v.val ≤ 2 := by omega
  exact le_trans (induced_neighbor_card_le (graph Γ) _ v)
    (le_trans (neighbor_card_le_degree Γ v.val) hdegree)

/-- Every actual outside connected component is exactly a simple path or a cycle.
The path case includes isolated vertices; unused isolated vertices can later be
removed by the support condition. -/
theorem outside_component_path_or_cycle (Γ : Finset (Finset V))
    (heven : Expansion.IsEven id Γ) (C : (outsideGraph Γ).ConnectedComponent) :
    (∃ (u v : C) (p : C.toSimpleGraph.Walk u v), p.IsPath ∧ (∀ x, x ∈ p.support) ∧
      C.toSimpleGraph = p.toSubgraph.spanningCoe) ∨
    (∃ (u : C) (p : C.toSimpleGraph.Walk u u), p.IsCycle ∧ (∀ x, x ∈ p.support) ∧
      C.toSimpleGraph = p.toSubgraph.spanningCoe) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  apply SKGraphShapes.exists_path_or_cycle C.toSimpleGraph C.connected_toSimpleGraph
  intro x
  exact le_trans (induced_neighbor_card_le (outsideGraph Γ) C.supp x)
    (outside_neighbor_card_le_two Γ heven x.val)

end SpinGlass.SKOutsideClassification
