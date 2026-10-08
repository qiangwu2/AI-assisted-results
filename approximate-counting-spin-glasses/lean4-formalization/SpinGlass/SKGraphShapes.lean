import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Finite connected graphs of maximum degree two

A longest simple path contains every vertex of a finite connected graph whose
neighbor sets have cardinality at most two. This is the traversal classification
needed for the outside components of an SK graph.
-/

noncomputable section

namespace SpinGlass.SKGraphShapes

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- At an internal vertex, a simple path exhausts every possible graph neighbor. -/
theorem internal_neighborSet_eq {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hdeg : ∀ x, (G.neighborSet x).ncard ≤ 2) {i : ℕ} (hi : i ≠ 0) (hil : i < p.length) :
    p.toSubgraph.neighborSet (p.getVert i) = G.neighborSet (p.getVert i) := by
  apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset _)
  rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hi hil]
  exact hdeg _

/-- A longest path has no graph edge from its support to a vertex outside it. -/
theorem longest_path_closed {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hdeg : ∀ x, (G.neighborSet x).ncard ≤ 2)
    (hmax : ∀ u' v' (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) :
    ∀ x ∈ p.support, ∀ y, G.Adj x y → y ∈ p.support := by
  intro x hx y hxy
  by_cases hy : y ∈ p.support
  · exact hy
  · by_cases hxu : x = u
    · subst x
      have hq := hmax y v (p.cons hxy.symm) (hp.cons hy)
      simp at hq
    · by_cases hxv : x = v
      · subst x
        have hq := hmax u y (p.concat hxy) (hp.concat hy hxy)
        simp at hq
      · obtain ⟨i, hix, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hx
        have hi : i ≠ 0 := by intro hi; subst i; simp at hix; exact hxu hix.symm
        have hil' : i < p.length := by
          by_contra hnot
          have heq : i = p.length := by omega
          subst i
          simp at hix
          exact hxv hix.symm
        have heq := internal_neighborSet_eq G p hp hdeg hi hil'
        have hyn : y ∈ p.toSubgraph.neighborSet x := by
          rw [← hix, heq]
          simpa [hix] using hxy
        have hadj : p.toSubgraph.Adj x y := hyn
        have hyv : y ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert hadj.symm
        exact p.mem_verts_toSubgraph.mp hyv

/-- Reachability cannot leave a vertex set closed under graph adjacency. -/
theorem reachable_stays {S : Set V}
    (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S)
    {u v : V} (hu : u ∈ S) (huv : G.Reachable u v) : v ∈ S := by
  obtain ⟨p⟩ := huv
  have hwalk : ∀ a b (q : G.Walk a b), a ∈ S → b ∈ S := by
    intro a b q
    induction q with
    | nil => exact id
    | @cons a b c hab q ih => exact fun ha => ih (hclosed a ha b hab)
  exact hwalk u v p hu

/-- A finite connected graph with maximum degree two has a spanning simple path. -/
theorem exists_spanning_path (hconn : G.Connected)
    (hdeg : ∀ x, (G.neighborSet x).ncard ≤ 2) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ x, x ∈ p.support := by
  classical
  letI : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u, v, p, hp, ?_⟩
  intro x
  exact reachable_stays G (longest_path_closed G p hp hdeg hmax)
    p.start_mem_support (hconn u x)

/-- Any edge omitted by a spanning path must join its two endpoints. -/
theorem missing_edge_endpoints {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hdeg : ∀ x, (G.neighborSet x).ncard ≤ 2) (hspan : ∀ x, x ∈ p.support)
    {x y : V} (hxy : G.Adj x y) (hmissing : ¬p.toSubgraph.Adj x y) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hend : ∀ a b, G.Adj a b → ¬p.toSubgraph.Adj a b → a = u ∨ a = v := by
    intro a b hab hnot
    by_contra hne
    have hnu : a ≠ u := fun he => hne (Or.inl he)
    have hnv : a ≠ v := fun he => hne (Or.inr he)
    obtain ⟨i, hia, hil⟩ := Walk.mem_support_iff_exists_getVert.mp (hspan a)
    have hi : i ≠ 0 := by intro hi; subst i; simp at hia; exact hnu hia.symm
    have hil' : i < p.length := by
      by_contra hn
      have hei : i = p.length := by omega
      subst i
      simp at hia
      exact hnv hia.symm
    have heq := internal_neighborSet_eq G p hp hdeg hi hil'
    apply hnot
    change b ∈ p.toSubgraph.neighborSet a
    rw [← hia, heq]
    simpa [hia] using hab
  have hx := hend x y hxy hmissing
  have hy := hend y x hxy.symm (fun h => hmissing h.symm)
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact False.elim (G.irrefl hxy)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact False.elim (G.irrefl hxy)

/-- A connected maximum-degree-two graph is exactly a path or exactly a cycle. -/
theorem exists_path_or_cycle (hconn : G.Connected)
    (hdeg : ∀ x, (G.neighborSet x).ncard ≤ 2) :
    (∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ (∀ x, x ∈ p.support) ∧
      G = p.toSubgraph.spanningCoe) ∨
    (∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ (∀ x, x ∈ p.support) ∧
      G = p.toSubgraph.spanningCoe) := by
  classical
  obtain ⟨u, v, p, hp, hspan⟩ := exists_spanning_path G hconn hdeg
  by_cases hfull : ∀ x y, G.Adj x y → p.toSubgraph.Adj x y
  · left
    refine ⟨u, v, p, hp, hspan, ?_⟩
    ext x y
    exact ⟨hfull x y, p.toSubgraph.adj_sub⟩
  · obtain ⟨x, hx⟩ := not_forall.mp hfull
    obtain ⟨y, hy⟩ := not_forall.mp hx
    obtain ⟨hxy, hmissing⟩ := _root_.not_imp.mp hy
    have huv : G.Adj u v ∧ ¬p.toSubgraph.Adj u v := by
      rcases missing_edge_endpoints G p hp hdeg hspan hxy hmissing with h | h
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨hxy, hmissing⟩
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨hxy.symm, fun h => hmissing h.symm⟩
    let c : G.Walk v v := p.cons huv.1.symm
    have hc : c.IsCycle := by
      apply (Walk.cons_isCycle_iff p huv.1.symm).mpr
      refine ⟨hp, ?_⟩
      intro he
      exact huv.2 (Walk.adj_toSubgraph_iff_mem_edges.mpr he).symm
    right
    refine ⟨v, c, hc, ?_, ?_⟩
    · intro z
      exact List.mem_cons_of_mem v (hspan z)
    · ext a b
      constructor
      · intro hab
        change c.toSubgraph.Adj a b
        rw [Walk.adj_toSubgraph_iff_mem_edges]
        simp only [c, Walk.edges_cons, List.mem_cons]
        by_cases hpab : p.toSubgraph.Adj a b
        · exact Or.inr (Walk.adj_toSubgraph_iff_mem_edges.mp hpab)
        · left
          rcases missing_edge_endpoints G p hp hdeg hspan hab hpab with h | h
          · obtain ⟨rfl, rfl⟩ := h
            exact Sym2.eq_swap
          · obtain ⟨rfl, rfl⟩ := h
            rfl
      · exact c.toSubgraph.adj_sub

end SpinGlass.SKGraphShapes
