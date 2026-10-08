import SpinGlass.SKPrimitiveCatalog
import SpinGlass.SKTraversalPrimitives

/-!
# Reconstruction of full primitive blocks from their spanning outside traversals

The final equality follows from equality of the actual incident-edge sets:
a constructed subgraph with degree two at every used outside vertex already
exhausts a degree-two block whose every edge touches the outside.
-/
noncomputable section
namespace SpinGlass.SKPrimitiveCatalogWalk
open Finset SimpleGraph SpinGlass.SKPrimitiveCatalog SpinGlass.SKTraversal
open SpinGlass.SKBlockPartition
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Incidence saturation upgrades a constructed degree-two subgraph to the full block. -/
theorem saturated_eq {A : Finset V} {K H : Finset (Finset V)}
    (hout : ∀ e∈K, ∃ v∈e, v∉A) (hd : OutsideDegreeTwo id A K)
    (hsub : H⊆K) (hH : ∀ v∈outside id A K, SpinGlass.Expansion.degree id H v=2) : H=K := by
  apply Finset.Subset.antisymm hsub
  intro e he
  obtain ⟨v,hve,hvA⟩ := hout e he
  have hvo := mem_outside_of_edge he hve hvA
  have hcard : (K.filter (fun e => v∈e)).card ≤ (H.filter (fun e => v∈e)).card := by
    change SpinGlass.Expansion.degree id K v ≤ SpinGlass.Expansion.degree id H v
    rw [hd v hvo, hH v hvo]
  have hsame : H.filter (fun e => v∈e)=K.filter (fun e => v∈e) :=
    Finset.eq_of_subset_of_card_le (fun e h => Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp h).1,
      (Finset.mem_filter.mp h).2⟩) hcard
  have he' : e∈H.filter (fun e => v∈e) := hsame ▸ Finset.mem_filter.mpr ⟨he,hve⟩
  exact (Finset.mem_filter.mp he').1

/-- All consecutive edges of a mapped graph walk are genuine input edges. -/
theorem walk_pathEdges_subset {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    (ι : W → V) (K : Finset (Finset V))
    (hG : ∀ u v, G.Adj u v → ({ι u,ι v}:Finset V)∈K)
    {u v : W} (p : G.Walk u v) : pathEdges (p.support.map ι)⊆K := by
  induction p with
  | nil => simp [pathEdges]
  | @cons u v z huv p ih =>
    have hstep : pathEdges ((Walk.cons huv p).support.map ι) =
        insert {ι u,ι v} (pathEdges (p.support.map ι)) := by cases p <;> rfl
    rw [hstep]
    exact Finset.insert_subset_iff.mpr ⟨hG u v huv,ih⟩

/-- The outside walk uses only edges of its block. -/
theorem used_walk_subset (A : Finset V) (K : Finset (Finset V))
    {u v : outside id A K} (p : (usedGraph A K).Walk u v) :
    pathEdges (p.support.map Subtype.val)⊆K := by
  apply walk_pathEdges_subset (usedGraph A K) Subtype.val K
  intro x y hxy
  exact hxy.2

/-- Closing a list whose final vertex is the distinguished starting vertex
recovers exactly the edge set of the corresponding closed walk. -/
theorem cycleEdges_tail_eq {a : V} {l : List V} (hne : l≠[])
    (hlast : l.getLast hne=a) : cycleEdges l=pathEdges (a::l) := by
  obtain ⟨x,xs,rfl⟩ := List.exists_cons_of_ne_nil hne
  change pathEdges ((x::xs)++[x])=insert {a,x} (pathEdges (x::xs))
  rw [pathEdges_concat, hlast]

/-- The tail of a simple closed walk is its injective cycle vertex list. -/
theorem cycle_walk_list {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    (ι : W → V) (hι : Function.Injective ι) {u : W} (p : G.Walk u u) (hp : p.IsCycle) :
    (p.support.tail.map ι).Nodup ∧ 3≤(p.support.tail.map ι).length ∧
      cycleEdges (p.support.tail.map ι)=pathEdges (p.support.map ι) := by
  have hn : p.support.tail.Nodup := hp.support_nodup
  refine ⟨hn.map hι, ?_, ?_⟩
  · simpa only [List.length_map, List.length_tail, Walk.length_support, Nat.add_sub_cancel]
      using hp.three_le_length
  · cases p with
    | nil => exact False.elim (hp.ne_nil rfl)
    | @cons u v u huv p =>
      have hne : (p.support.map ι)≠[] := by simp
      have hlast : (p.support.map ι).getLast hne=ι u := by
        rw [List.getLast_map, Walk.getLast_support]
      simpa only [Walk.support_cons, List.tail_cons, List.map_cons] using
        cycleEdges_tail_eq hne hlast

/-- A spanning cycle already saturates the entire degree-two block. -/
theorem reconstruct_cycle (A : Finset V) (K : Finset (Finset V))
    (hout : ∀ e∈K, ∃ v∈e, v∉A) (hd : OutsideDegreeTwo id A K)
    {u : outside id A K} (p : (usedGraph A K).Walk u u)
    (hp : p.IsCycle) (hspan : ∀ x, x∈p.support) :
    ∃ l : List V, l.Nodup ∧ 3≤l.length ∧ (∀ v∈l, v∉A) ∧
      l.toFinset=outside id A K ∧ K=cycleEdges l := by
  let l := p.support.tail.map Subtype.val
  obtain ⟨hn,hlen,he⟩ := cycle_walk_list (usedGraph A K) Subtype.val Subtype.val_injective p hp
  have hcover : ∀ v∈outside id A K, v∈l := by
    intro v hv
    have hmem : (⟨v,hv⟩ : outside id A K)∈p.support.tail := by
      by_cases h : (⟨v,hv⟩ : outside id A K)=u
      · subst u
        exact Walk.end_mem_tail_support hp.not_nil
      · have hs := hspan ⟨v,hv⟩
        rw [← p.cons_tail_support, List.mem_cons] at hs
        exact hs.resolve_left h
    exact List.mem_map.mpr ⟨⟨v,hv⟩,hmem,rfl⟩
  have houtl : ∀ v∈l, v∈outside id A K := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact w.property
  refine ⟨l,hn,hlen,fun v hv => (Finset.mem_sdiff.mp (houtl v hv)).2,?_,?_⟩
  · ext v
    exact ⟨fun h => houtl v (List.mem_toFinset.mp h), fun h => List.mem_toFinset.mpr (hcover v h)⟩
  · symm
    apply saturated_eq hout hd
    · rw [show cycleEdges l=pathEdges (p.support.map Subtype.val) from he]
      exact used_walk_subset A K p
    · intro v hv
      rw [cycleEdges_degree hn hlen, if_pos (hcover v hv)]

/-- Decomposition of a branch path into its two attachments and its outside walk. -/
theorem betweenEdges_decompose (a b x : V) (xs : List V) :
    betweenEdges a b (x::xs)=insert {b,x}
      (insert {(x::xs).getLast (by simp),a} (pathEdges (x::xs))) := by
  change insert {b,x} (pathEdges ((x::xs)++[a]))=_
  rw [pathEdges_concat]

theorem betweenEdges_walk {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    (ι : W → V) {u v : W} (p : G.Walk u v) (a b : V) :
    betweenEdges a b (p.support.map ι)=insert {b,ι u}
      (insert {ι v,a} (pathEdges (p.support.map ι))) := by
  have hlast : (p.support.map ι).getLast (by simp)=ι v := by
    rw [List.getLast_map, Walk.getLast_support]
  have hsupport : ι u::(p.support.tail.map ι)=p.support.map ι := by
    simpa only [List.map_cons] using congrArg (List.map ι) p.cons_tail_support
  have hlast' : (ι u::(p.support.tail.map ι)).getLast (by simp)=ι v := by
    simpa only [hsupport] using hlast
  rw [← hsupport, betweenEdges_decompose, hlast']

/-- A nontrivial exact spanning path has one branch attachment at each endpoint. -/
theorem path_attachments (A : Finset V) (K : Finset (Finset V))
    (h2 : ∀ e∈K, e.card=2) (hd : OutsideDegreeTwo id A K)
    {u v : outside id A K} (p : (usedGraph A K).Walk u v)
    (hp : p.IsPath) (hn : ¬p.Nil) (hg : usedGraph A K=p.toSubgraph.spanningCoe) :
    (∃ b∈A, ({u.val,b}:Finset V)∈K) ∧ (∃ a∈A, ({v.val,a}:Finset V)∈K) := by
  have hs : ((usedGraph A K).neighborSet u).ncard=1 := by
    have he : (usedGraph A K).neighborSet u=p.toSubgraph.neighborSet u :=
      congrArg (fun G : SimpleGraph (outside id A K) => G.neighborSet u) hg
    rw [he, hp.neighborSet_toSubgraph_startpoint hn, Set.ncard_singleton]
  have ht : ((usedGraph A K).neighborSet v).ncard=1 := by
    have he : (usedGraph A K).neighborSet v=p.toSubgraph.neighborSet v :=
      congrArg (fun G : SimpleGraph (outside id A K) => G.neighborSet v) hg
    rw [he, hp.neighborSet_toSubgraph_endpoint hn, Set.ncard_singleton]
  constructor
  · have h := usedGraph_add_attachments A K h2 hd u
    rw [hs] at h
    have hc : 0<(SpinGlass.SKAttachments.attachments K A u.val).card := by omega
    obtain ⟨b,hb⟩ := Finset.card_pos.mp hc
    have hb' := (mem_attachments A K u.val b).mp hb
    exact ⟨b,hb'.1,hb'.2.2⟩
  · have h := usedGraph_add_attachments A K h2 hd v
    rw [ht] at h
    have hc : 0<(SpinGlass.SKAttachments.attachments K A v.val).card := by omega
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hc
    have ha' := (mem_attachments A K v.val a).mp ha
    exact ⟨a,ha'.1,ha'.2.2⟩

/-- Every exact spanning outside path, including a singleton, reconstructs the
entire original block after its two actual branch attachments are restored. -/
theorem reconstruct_path (A : Finset V) (K : Finset (Finset V))
    (h2 : ∀ e∈K, e.card=2) (hout : ∀ e∈K, ∃ v∈e, v∉A)
    (hd : OutsideDegreeTwo id A K) {u v : outside id A K}
    (p : (usedGraph A K).Walk u v) (hp : p.IsPath)
    (hspan : ∀ x, x∈p.support) (hg : usedGraph A K=p.toSubgraph.spanningCoe) :
    ∃ a∈A, ∃ b∈A, ∃ l : List V,
      l.Nodup ∧ l≠[] ∧ (∀ w∈l, w∉A) ∧ l.toFinset=outside id A K ∧
      K=betweenEdges a b l ∧ (a=b → 2≤l.length) := by
  let l := p.support.map Subtype.val
  have hln : l.Nodup := hp.support_nodup.map Subtype.val_injective
  have hlne : l≠[] := by
    intro h
    have hh : p.support=[] := List.map_eq_nil_iff.mp h
    simpa using hh
  have hcover : ∀ w∈outside id A K, w∈l := by
    intro w hw
    exact List.mem_map.mpr ⟨⟨w,hw⟩,hspan ⟨w,hw⟩,rfl⟩
  have hlout : ∀ w∈l, w∉A := by
    intro w hw
    obtain ⟨w',hw',rfl⟩ := List.mem_map.mp hw
    exact (Finset.mem_sdiff.mp w'.property).2
  have hlset : l.toFinset=outside id A K := by
    ext w
    constructor
    · intro hw
      obtain ⟨w',hw',rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
      exact w'.property
    · intro hw; exact List.mem_toFinset.mpr (hcover w hw)
  by_cases hnil : p.Nil
  · have huv : u=v := hnil.eq
    subst v
    have heq : p=Walk.nil := hnil.eq_nil
    subst p
    have hs : ((usedGraph A K).neighborSet u).ncard=0 := by
      have he : (usedGraph A K).neighborSet u =
          ((usedGraph A K).singletonSubgraph u).neighborSet u :=
        congrArg (fun G : SimpleGraph (outside id A K) => G.neighborSet u) hg
      rw [he, SimpleGraph.neighborSet_singletonSubgraph, Set.ncard_empty]
    have h := usedGraph_add_attachments A K h2 hd u
    rw [hs, Nat.zero_add] at h
    obtain ⟨a,b,hab,habset⟩ := Finset.card_eq_two.mp h
    have ha' := (mem_attachments A K u.val a).mp (by rw [habset]; simp)
    have hb' := (mem_attachments A K u.val b).mp (by rw [habset]; simp)
    have ha : a∉l := fun hm => hlout a hm ha'.1
    have hb : b∉l := fun hm => hlout b hm hb'.1
    refine ⟨a,ha'.1,b,hb'.1,l,hln,hlne,hlout,hlset,?_,fun he => False.elim (hab he)⟩
    symm
    apply saturated_eq hout hd
    · change pathEdges [b,u.val,a]⊆K
      simp only [pathEdges, Finset.insert_subset_iff, Finset.empty_subset, and_true]
      exact ⟨by simpa [Finset.pair_comm] using hb'.2.2,ha'.2.2⟩
    · intro w hw
      rw [betweenEdges_degree hab hln ha hb]
      have hwa : w≠a := fun he => (Finset.mem_sdiff.mp hw).2 (he ▸ ha'.1)
      have hwb : w≠b := fun he => (Finset.mem_sdiff.mp hw).2 (he ▸ hb'.1)
      simp [hwa,hwb,hcover w hw]
  · obtain ⟨⟨b,hbA,hbu⟩,⟨a,haA,hav⟩⟩ := path_attachments A K h2 hd p hp hnil hg
    have ha : a∉l := fun hm => hlout a hm haA
    have hb : b∉l := fun hm => hlout b hm hbA
    have hllen : 2≤l.length := by
      have h := Walk.not_nil_iff_lt_length.mp hnil
      simpa only [l,List.length_map,Walk.length_support] using Nat.succ_le_succ h
    refine ⟨a,haA,b,hbA,l,hln,hlne,hlout,hlset,?_,fun _ => hllen⟩
    symm
    apply saturated_eq hout hd
    · rw [show betweenEdges a b l=insert {b,u.val}
        (insert {v.val,a} (pathEdges (p.support.map Subtype.val))) from
          betweenEdges_walk (usedGraph A K) Subtype.val p a b]
      exact Finset.insert_subset_iff.mpr ⟨by simpa [Finset.pair_comm] using hbu,
        Finset.insert_subset_iff.mpr ⟨hav,used_walk_subset A K p⟩⟩
    · intro w hw
      have hwa : w≠a := fun he => (Finset.mem_sdiff.mp hw).2 (he ▸ haA)
      have hwb : w≠b := fun he => (Finset.mem_sdiff.mp hw).2 (he ▸ hbA)
      by_cases hab : a=b
      · subst b
        change SpinGlass.Expansion.degree id (rootedEdges a l) w=2
        rw [rootedEdges_degree hln ha hllen]
        simp [hcover w hw]
      · rw [betweenEdges_degree hab hln ha hb]
        simp [hwa,hwb,hcover w hw]

/-- Exhaustive concrete list catalog of every nonempty connected primitive block.
The four alternatives are direct branch edges, distinct-branch paths, returns
to one branch, and cycles entirely outside the branch set. -/
theorem primitive_classification (A : Finset V) (K : Finset (Finset V))
    (hne : K.Nonempty) (hc : SpinGlass.SKBlockPartition.Connected id A K)
    (h2 : ∀ e∈K, e.card=2) (hd : OutsideDegreeTwo id A K) :
    (∃ a∈A, ∃ b∈A, a≠b ∧ K={{a,b}}) ∨
    (∃ a∈A, ∃ b∈A, a≠b ∧ ∃ l : List V,
      l.Nodup ∧ 1≤l.length ∧ (∀ v∈l, v∉A) ∧ l.toFinset=outside id A K ∧
        K=betweenEdges a b l) ∨
    (∃ a∈A, ∃ l : List V,
      l.Nodup ∧ 2≤l.length ∧ (∀ v∈l, v∉A) ∧ l.toFinset=outside id A K ∧
        K=rootedEdges a l) ∨
    (∃ l : List V,
      l.Nodup ∧ 3≤l.length ∧ (∀ v∈l, v∉A) ∧ l.toFinset=outside id A K ∧
        K=cycleEdges l) := by
  rcases direct_or_traversal A K hne hc h2 hd with hdir | ⟨hout,hpath | hcycle⟩
  · exact Or.inl hdir
  · obtain ⟨u,v,p,hp,hspan,hg⟩ := hpath
    obtain ⟨a,ha,b,hb,l,hln,hlne,hlout,hlset,heq,hlen⟩ :=
      reconstruct_path A K h2 hout hd p hp hspan hg
    by_cases hab : a=b
    · subst b
      exact Or.inr (Or.inr (Or.inl ⟨a,ha,l,hln,hlen rfl,hlout,hlset,heq⟩))
    · exact Or.inr (Or.inl ⟨a,ha,b,hb,hab,l,hln,
        (by by_contra h; have hz : l.length=0 := by omega
            exact hlne (List.length_eq_zero_iff.mp hz)),hlout,hlset,heq⟩)
  · obtain ⟨u,p,hp,hspan,hg⟩ := hcycle
    exact Or.inr (Or.inr (Or.inr (reconstruct_cycle A K hout hd p hp hspan)))

end SpinGlass.SKPrimitiveCatalogWalk
