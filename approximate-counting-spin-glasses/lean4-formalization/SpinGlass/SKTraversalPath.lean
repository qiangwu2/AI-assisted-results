import SpinGlass.ColorCycleChain
import SpinGlass.SKOutsideClassification

/-!
# Reconstruction of an undirected simple path from its edge set

The objects here are actual ordered vertex lists, as enumerated by ColorPath.
The reconstruction lemma is the combinatorial basis for the orientation factors.
-/

noncomputable section
namespace SpinGlass.SKTraversal
open Finset
variable {V : Type*} [DecidableEq V]

/-- Actual unordered consecutive pairs of a vertex list. -/
def pathEdges : List V → Finset (Finset V)
  | [] => ∅
  | [_] => ∅
  | x::y::xs => insert {x,y} (pathEdges (y::xs))

theorem mem_pathEdges_vertices {l : List V} {e : Finset V} (he : e∈pathEdges l) :
    ∀ x∈e, x∈l := by
  induction l with
  | nil => simp [pathEdges] at he
  | cons a l ih =>
    cases l with
    | nil => simp [pathEdges] at he
    | cons b l =>
      simp only [pathEdges, Finset.mem_insert] at he
      rcases he with rfl | he
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp
      · intro x hx; exact List.mem_cons_of_mem a (ih he x hx)

theorem not_mem_pathEdges {l : List V} {x : V} (hx : x∉l) {e : Finset V} (hxe : x∈e) :
    e∉pathEdges l := fun he => hx (mem_pathEdges_vertices he x hxe)

theorem pathEdges_pair {x y : V} : pathEdges [x,y] = {{x,y}} := by simp [pathEdges]

theorem pathEdges_concat (l : List V) (x y : V) :
    pathEdges ((x::l)++[y]) = insert {(x::l).getLast (by simp), y} (pathEdges (x::l)) := by
  induction l generalizing x with
  | nil => simp [pathEdges]
  | cons z l ih =>
    simpa only [List.cons_append, pathEdges, List.getLast_cons_cons, Finset.insert_comm] using
      congrArg (insert {x,z}) (ih z)

@[simp] theorem pathEdges_reverse (l : List V) : pathEdges l.reverse = pathEdges l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons y l =>
      rw [List.reverse_cons]
      have hne : (y::l).reverse ≠ [] := List.reverse_ne_nil_iff.mpr (by simp)
      obtain ⟨a, as, heq⟩ := List.exists_cons_of_ne_nil hne
      rw [heq, pathEdges_concat]
      have hlast : (a::as).getLast (by simp) = y := by
        have h := List.getLast_reverse (l := y::l) (by simp)
        simpa only [heq, List.head_cons] using h
      rw [hlast, ← heq, ih]
      simp [pathEdges, Finset.pair_comm]

/-- An endpoint of a nodup list has exactly its first consecutive edge. -/
theorem head_pair_of_mem {x y z : V} {l : List V} (hn : (x::y::l).Nodup)
    (he : ({x,z}:Finset V)∈pathEdges (x::y::l)) : z=y := by
  rw [pathEdges, Finset.mem_insert] at he
  rcases he with he | he
  · have hy : y∈({x,z}:Finset V) := by rw [he]; simp
    have hxy : x≠y := (List.nodup_cons.mp hn).1 ∘ (by exact fun h => h ▸ List.mem_cons_self)
    have hyz : y=x ∨ y=z := by simpa using hy
    exact hyz.elim (fun h => False.elim (hxy h.symm)) Eq.symm
  · exact False.elim ((not_mem_pathEdges (List.nodup_cons.mp hn).1 (by simp)) he)

/-- Removing the endpoint edge of a simple path leaves exactly the tail edges. -/
theorem erase_head_edge {x y : V} {l : List V} (hn : (x::y::l).Nodup) :
    (pathEdges (x::y::l)).erase {x,y} = pathEdges (y::l) := by
  rw [pathEdges, Finset.erase_insert]
  exact not_mem_pathEdges (List.nodup_cons.mp hn).1 (by simp)

/-- A nonempty simple path is uniquely reconstructed once its starting vertex is fixed. -/
theorem pathEdges_head_injective {l q : List V} (hl : l.Nodup) (hq : q.Nodup)
    (hh : l.head?=q.head?) (he : pathEdges l=pathEdges q) : l=q := by
  induction l generalizing q with
  | nil => cases q <;> simp_all
  | cons x l ih =>
    cases q with
    | nil => simp at hh
    | cons x' q =>
      have hx : x=x' := by simpa using hh
      subst x'
      cases l with
      | nil =>
        cases q with
        | nil => rfl
        | cons z q =>
          have hem : ({x,z}:Finset V)∈pathEdges (x::z::q) := by simp [pathEdges]
          rw [← he] at hem
          simp [pathEdges] at hem
      | cons y l =>
        cases q with
        | nil =>
          have hem : ({x,y}:Finset V)∈pathEdges (x::y::l) := by simp [pathEdges]
          rw [he] at hem
          simp [pathEdges] at hem
        | cons z q =>
          have hyz : y=z := by
            apply head_pair_of_mem hq
            rw [← he]
            simp [pathEdges]
          subst z
          have het : pathEdges (y::l)=pathEdges (y::q) := by
            rw [← erase_head_edge hl, he, erase_head_edge hq]
          exact congrArg (List.cons x)
            (ih (List.nodup_cons.mp hl).2 (List.nodup_cons.mp hq).2 rfl het)

/-- Consecutive edges are distinct for an injective vertex list. -/
theorem pathEdges_card {l : List V} (hn : l.Nodup) : (pathEdges l).card = l.length-1 := by
  induction l with
  | nil => simp [pathEdges]
  | cons x l ih =>
    cases l with
    | nil => simp [pathEdges]
    | cons y l =>
      rw [pathEdges, Finset.card_insert_of_notMem
        (not_mem_pathEdges (List.nodup_cons.mp hn).1 (by simp)),
        ih (List.nodup_cons.mp hn).2]
      simp

/-- Add a distinguished root at both ends of an interior chain. -/
def rootedEdges (root : V) (l : List V) : Finset (Finset V) :=
  pathEdges (root::(l++[root]))

@[simp] theorem rootedEdges_reverse (root : V) (l : List V) :
    rootedEdges root l.reverse = rootedEdges root l := by
  unfold rootedEdges
  have he : root::(l.reverse++[root]) = (root::(l++[root])).reverse := by simp
  rw [he, pathEdges_reverse]

/-- Cycle edges obtained by closing the ordered vertex list. -/
def cycleEdges : List V → Finset (Finset V)
  | [] => ∅
  | root::l => rootedEdges root l

end SpinGlass.SKTraversal
