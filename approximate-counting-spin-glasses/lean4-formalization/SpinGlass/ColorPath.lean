import SpinGlass.SKCoefficient
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Correctness of the color-subset chain recurrence

Vertices in a chain are listed in reverse traversal order, so the head is its
current endpoint. The implementation is the signed recurrence (65), with a depth
parameter permitting structural recursion. The reference enumeration is an
explicit finite list of chains; no path-weight identity is assumed.
-/

noncomputable section

namespace SpinGlass.ColorPath

open scoped BigOperators

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- Enumerate the colorful chains reaching `j` and using exactly `S`, up to depth `n`. -/
def chains (χ : V → C) : ℕ → Finset C → V → List (List V)
  | 0, _, _ => []
  | n + 1, S, j =>
      if S = {χ j} then [[j]]
      else if χ j ∈ S then
        (Finset.univ.toList : List V).flatMap
          (fun i => (chains χ n (S.erase (χ j)) i).map (List.cons j))
      else []

/-- The actual dynamic-programming values, with arbitrary real signed edge weights. -/
def table (χ : V → C) (start : V → ℝ) (w : V → V → ℝ) : ℕ → Finset C → V → ℝ
  | 0, _, _ => 0
  | n + 1, S, j =>
      if S = {χ j} then start j
      else if χ j ∈ S then ∑ i, table χ start w n (S.erase (χ j)) i * w i j
      else 0

/-- The exact ordered-chain weight, with the first edge represented by `start`. -/
def weight (start : V → ℝ) (w : V → V → ℝ) : List V → ℝ
  | [] => 0
  | [j] => start j
  | j :: i :: rest => weight start w (i :: rest) * w i j

/-- Every generated chain has the asserted endpoint. -/
theorem head_of_mem_chains (χ : V → C) (n : ℕ) (S : Finset C) (j : V)
    {l : List V} (hl : l ∈ chains χ n S j) : l.head? = some j := by
  cases n with
  | zero => simp [chains] at hl
  | succ n =>
    simp only [chains] at hl
    split at hl
    · have hl' : l = [j] := by simpa using hl
      subst l
      rfl
    · split at hl
      · obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp hl
        obtain ⟨li, htail, rfl⟩ := List.mem_map.mp hm
        rfl
      · simp at hl

/-- Every generated chain is colorful and uses exactly its advertised color set. -/
theorem colors_of_mem_chains (χ : V → C) (n : ℕ) (S : Finset C) (j : V)
    {l : List V} (hl : l ∈ chains χ n S j) :
    (l.map χ).Nodup ∧ (l.map χ).toFinset = S := by
  induction n generalizing S j l with
  | zero => simp [chains] at hl
  | succ n ih =>
    simp only [chains] at hl
    split at hl
    next hS =>
      have hl' : l = [j] := by simpa using hl
      subst l
      simp [hS]
    next hS =>
      split at hl
      next hj =>
        obtain ⟨i, hi, hli⟩ := List.mem_flatMap.mp hl
        obtain ⟨li, htail, rfl⟩ := List.mem_map.mp hli
        obtain ⟨hnd, hc⟩ := ih (S.erase (χ j)) i htail
        have hnot : χ j ∉ li.map χ := by
          intro hmem
          have hm : χ j ∈ (li.map χ).toFinset := by simpa using hmem
          rw [hc] at hm
          exact Finset.notMem_erase _ _ hm
        constructor
        · simpa using List.nodup_cons.mpr ⟨hnot, hnd⟩
        · simpa [hc] using Finset.insert_erase hj
      next hj => simp at hl

/-- A chain cannot contain more vertices than the available recursion depth. -/
theorem length_le_depth_of_mem_chains (χ : V → C) (n : ℕ) (S : Finset C) (j : V)
    {l : List V} (hl : l ∈ chains χ n S j) : l.length ≤ n := by
  induction n generalizing S j l with
  | zero => simp [chains] at hl
  | succ n ih =>
    simp only [chains] at hl
    split at hl
    next hS =>
      have hl' : l = [j] := by simpa using hl
      subst l
      simp
    next hS =>
      split at hl
      next hj =>
        obtain ⟨i, hi, hli⟩ := List.mem_flatMap.mp hl
        obtain ⟨li, htail, rfl⟩ := List.mem_map.mp hli
        exact Nat.succ_le_succ (ih (S.erase (χ j)) i htail)
      next hj => simp at hl

/-- The advertised color count equals the number of vertices in every chain. -/
theorem length_of_mem_chains (χ : V → C) (n : ℕ) (S : Finset C) (j : V)
    {l : List V} (hl : l ∈ chains χ n S j) : l.length = S.card := by
  obtain ⟨hn, hc⟩ := colors_of_mem_chains χ n S j hl
  have hcard := List.toFinset_card_of_nodup hn
  simpa [hc] using hcard.symm

/-- Every colorful ordered chain is included once sufficient depth is available. -/
theorem mem_chains_of_properties (χ : V → C) (n : ℕ) (S : Finset C) (j : V)
    {l : List V} (hh : l.head? = some j) (hc : (l.map χ).toFinset = S)
    (hn : (l.map χ).Nodup) (hlen : l.length ≤ n) : l ∈ chains χ n S j := by
  induction n generalizing S j l with
  | zero =>
    cases l <;> simp_all
  | succ n ih =>
    cases l with
    | nil => simp at hh
    | cons k rest =>
      have hk : k = j := by simpa using hh
      subst k
      cases rest with
      | nil =>
        have hS : S = {χ j} := by simpa using hc.symm
        simp [chains, hS]
      | cons i rest =>
        have hnd := List.nodup_cons.mp hn
        have hnot : χ j ∉ ((i :: rest).map χ).toFinset := by
          simpa using hnd.1
        have hj : χ j ∈ S := by rw [← hc]; simp
        have hi : χ i ∈ S := by rw [← hc]; simp
        have hne : S ≠ {χ j} := by
          intro heq
          have heqij : χ i = χ j := by simpa [heq] using hi
          exact hnd.1 (by simp [heqij])
        have htailset : (((i :: rest).map χ).toFinset) = S.erase (χ j) := by
          calc
            ((i :: rest).map χ).toFinset =
                (insert (χ j) (((i :: rest).map χ).toFinset)).erase (χ j) := by
              exact (Finset.erase_insert hnot).symm
            _ = S.erase (χ j) := by rw [← hc]; simp
        have htail : i :: rest ∈ chains χ n (S.erase (χ j)) i :=
          ih (S.erase (χ j)) i rfl htailset hnd.2 (by simpa using hlen)
        simp only [chains, if_neg hne, if_pos hj]
        apply List.mem_flatMap.mpr
        refine ⟨i, by simp, ?_⟩
        exact List.mem_map.mpr ⟨i :: rest, htail, rfl⟩

/-- A precise, nonrecursive characterization of the enumerated objects. -/
theorem mem_chains_iff (χ : V → C) (n : ℕ) (S : Finset C) (j : V) (l : List V) :
    l ∈ chains χ n S j ↔ l.head? = some j ∧ (l.map χ).Nodup ∧
      (l.map χ).toFinset = S ∧ l.length ≤ n := by
  constructor
  · intro hl
    exact ⟨head_of_mem_chains χ n S j hl, (colors_of_mem_chains χ n S j hl).1,
      (colors_of_mem_chains χ n S j hl).2, length_le_depth_of_mem_chains χ n S j hl⟩
  · rintro ⟨hh, hn, hc, hlen⟩
    exact mem_chains_of_properties χ n S j hh hc hn hlen

/-- The reference enumeration never repeats the same ordered chain. -/
theorem chains_nodup (χ : V → C) (n : ℕ) (S : Finset C) (j : V) :
    (chains χ n S j).Nodup := by
  induction n generalizing S j with
  | zero => simp [chains]
  | succ n ih =>
    simp only [chains]
    split
    · simp
    · split
      · apply List.nodup_flatMap.mpr
        constructor
        · intro i hi
          exact (ih (S.erase (χ j)) i).map (fun l l' h => (List.cons.inj h).2)
        · apply (Finset.nodup_toList (Finset.univ : Finset V)).imp
          intro i k hik l hl hk
          obtain ⟨li, hli, rfl⟩ := List.mem_map.mp hl
          obtain ⟨lk, hlk, heq⟩ := List.mem_map.mp hk
          have heqtail : lk = li := (List.cons.inj heq).2
          subst lk
          apply hik
          exact Option.some.inj
            ((head_of_mem_chains χ n (S.erase (χ j)) i hli).symm.trans
              (head_of_mem_chains χ n (S.erase (χ j)) k hlk))
      · simp

/-- Adding a new endpoint multiplies by exactly its new edge weight. -/
theorem weight_cons_of_head (start : V → ℝ) (w : V → V → ℝ) (j i : V)
    {l : List V} (hl : l.head? = some i) :
    weight start w (j :: l) = weight start w l * w i j := by
  cases l with
  | nil => simp at hl
  | cons k rest =>
    have hk : k = i := by simpa using hl
    subst k
    rfl

private theorem sum_map_flatMap {A B : Type*} (l : List A) (f : A → List B) (g : B → ℝ) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- The computed table is the exact signed sum of the explicitly enumerated chains. -/
theorem table_eq_chain_sum (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (n : ℕ) (S : Finset C) (j : V) :
    table χ start w n S j = ((chains χ n S j).map (weight start w)).sum := by
  induction n generalizing S j with
  | zero => simp [table, chains]
  | succ n ih =>
    simp only [table, chains]
    split
    · simp [weight]
    · split
      · rw [sum_map_flatMap, Finset.sum_map_toList]
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih]
        simp only [List.map_map, Function.comp_def]
        have heq :
            ((chains χ n (S.erase (χ j)) i).map
              (fun l => weight start w (j :: l))).sum =
            ((chains χ n (S.erase (χ j)) i).map
              (fun l => weight start w l * w i j)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro l hl
          exact weight_cons_of_head start w j i
            (head_of_mem_chains χ n (S.erase (χ j)) i hl)
        rw [heq, List.sum_map_mul_right]
      · simp

/-- The depth-free color-subset table, evaluated with the exact necessary depth. -/
def pathTable (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (S : Finset C) (j : V) : ℝ := table χ start w S.card S j

@[simp] theorem pathTable_singleton (χ : V → C) (start : V → ℝ)
    (w : V → V → ℝ) (j : V) : pathTable χ start w {χ j} j = start j := by
  simp [pathTable, table]

/-- Equation (65) with strictly smaller color-subset dependencies. -/
theorem pathTable_recurrence (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (S : Finset C) (j : V) (hj : χ j ∈ S) (hcard : 2 ≤ S.card) :
    pathTable χ start w S j =
      ∑ i, pathTable χ start w (S.erase (χ j)) i * w i j := by
  have hne : S ≠ {χ j} := by
    intro heq
    simp [heq] at hcard
  have hcard' : S.card = (S.card - 1) + 1 := by omega
  have herase := Finset.card_erase_of_mem hj
  unfold pathTable
  conv_lhs => rw [hcard']
  simp only [table, if_neg hne, if_pos hj]
  simp only [herase]

/-- Invalid endpoint states vanish. -/
theorem pathTable_invalid (χ : V → C) (start : V → ℝ) (w : V → V → ℝ)
    (S : Finset C) (j : V) (hj : χ j ∉ S) : pathTable χ start w S j = 0 := by
  have hne : S ≠ {χ j} := by intro heq; simp [heq] at hj
  unfold pathTable
  cases S.card <;> simp [table, hj, hne]

/-- The recurrence sums each colorful ordered chain exactly once. -/
theorem pathTable_eq_finset_chain_sum (χ : V → C) (start : V → ℝ)
    (w : V → V → ℝ) (S : Finset C) (j : V) :
    pathTable χ start w S j =
      ∑ l ∈ (chains χ S.card S j).toFinset, weight start w l := by
  rw [pathTable, table_eq_chain_sum]
  exact (List.sum_toFinset _ (chains_nodup χ S.card S j)).symm

/-- The finite set being summed consists precisely of the desired colorful chains. -/
theorem mem_canonical_chains_iff (χ : V → C) (S : Finset C) (j : V) (l : List V) :
    l ∈ (chains χ S.card S j).toFinset ↔
      l.head? = some j ∧ (l.map χ).Nodup ∧ (l.map χ).toFinset = S := by
  simp only [List.mem_toFinset, mem_chains_iff]
  constructor
  · rintro ⟨hh, hn, hc, hlen⟩
    exact ⟨hh, hn, hc⟩
  · rintro ⟨hh, hn, hc⟩
    refine ⟨hh, hn, hc, ?_⟩
    have heq := List.toFinset_card_of_nodup hn
    simpa [hc] using Nat.le_of_eq heq.symm

/-- Color-subset processing is acyclic in increasing subset cardinality. -/
theorem dependency_card_lt (S : Finset C) (c : C) (hc : c ∈ S) :
    (S.erase c).card < S.card := Finset.card_erase_lt_of_mem hc

/-- Per root, the actual table has `2^L N` possible subset/endpoint coordinates. -/
theorem table_state_count (N L : ℕ) :
    Fintype.card (Finset (Fin L) × Fin N) = 2 ^ L * N := by
  simp [Fintype.card_prod, Fintype.card_finset]

/-- Trying every predecessor at each state visits `2^L N^2` triples. -/
theorem table_update_count (N L : ℕ) :
    Fintype.card (Finset (Fin L) × Fin N × Fin N) = 2 ^ L * N ^ 2 := by
  simp [Fintype.card_prod, Fintype.card_finset, pow_two, Nat.mul_assoc]

end SpinGlass.ColorPath
