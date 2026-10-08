import Std
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Finite incidence counting

These proofs use finite lists as enumerations of vertices and edges. For a
simple hypergraph those lists can be chosen without repetitions. The counting
identities also hold with repetitions, so no distinctness hypothesis is needed
for the bounds. Incidence is explicit, and uniformity is expressed by requiring
each edge to meet exactly `p` entries of the vertex enumeration.
-/

namespace SpinGlass.Incidence

/-- A finite sum, with multiplicities given by the enumeration. -/
def sumOver (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum

@[simp] theorem sumOver_nil (f : α → Nat) : sumOver [] f = 0 := rfl
@[simp] theorem sumOver_cons (x : α) (xs : List α) (f : α → Nat) :
    sumOver (x :: xs) f = f x + sumOver xs f := by
  simp [sumOver]

theorem sumOver_add (xs : List α) (f g : α → Nat) :
    sumOver xs (fun x => f x + g x) = sumOver xs f + sumOver xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [sumOver_cons, ih]; omega

theorem sumOver_zero (xs : List α) : sumOver xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Interchanging the two finite sums counts the same incidences. -/
theorem sumOver_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumOver xs (fun x => sumOver ys (f x)) =
      sumOver ys (fun y => sumOver xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [sumOver_zero]
  | cons x xs ih => simp [sumOver_add, ih]

theorem sumOver_eq_const (xs : List α) (f : α → Nat) (p : Nat)
    (h : ∀ x ∈ xs, f x = p) : sumOver xs f = p * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : f x = p := h x (by simp)
    have ht : ∀ y ∈ xs, f y = p := by
      intro y hy
      exact h y (by simp [hy])
    simp [hx, ih ht, Nat.mul_add, Nat.add_comm]

/-- Counting vertices whose degree reaches a threshold is bounded by degree mass. -/
theorem threshold_count_bound (xs : List α) (f : α → Nat) (t : Nat) :
    t * (xs.filter (fun x => t ≤ f x)).length ≤ sumOver xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : t ≤ f x
    · simp [hx, Nat.mul_add, sumOver_cons]
      omega
    · simp [hx, sumOver_cons]
      omega

/-- Counting positive degrees is bounded by degree mass if each is at least `t`. -/
theorem positive_count_bound (xs : List α) (f : α → Nat) (t : Nat)
    (h : ∀ x ∈ xs, 0 < f x → t ≤ f x) :
    t * (xs.filter (fun x => 0 < f x)).length ≤ sumOver xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, 0 < f y → t ≤ f y := by
      intro y hy
      exact h y (by simp [hy])
    have hi := ih ht
    by_cases hx : 0 < f x
    · have hb := h x (by simp) hx
      simp [hx, Nat.mul_add, sumOver_cons]
      omega
    · simp [hx, sumOver_cons]
      omega

/-- Degree in an explicitly specified finite incidence relation. -/
def degree (edges : List β) (incident : α → β → Bool) (v : α) : Nat :=
  sumOver edges (fun e => if incident v e then 1 else 0)

/-- Number of enumerated vertices incident with an edge. -/
def edgeSize (vertices : List α) (incident : α → β → Bool) (e : β) : Nat :=
  sumOver vertices (fun v => if incident v e then 1 else 0)

/-- Enumerated vertices used by at least one edge. -/
def support (vertices : List α) (edges : List β) (incident : α → β → Bool) : List α :=
  vertices.filter (fun v => 0 < degree edges incident v)

/-- Enumerated branching vertices, of degree at least four. -/
def branch (vertices : List α) (edges : List β) (incident : α → β → Bool) : List α :=
  vertices.filter (fun v => 4 ≤ degree edges incident v)

/-- The incidence version of the handshaking identity. -/
theorem sum_degrees_eq_sum_edgeSizes (vertices : List α) (edges : List β)
    (incident : α → β → Bool) :
    sumOver vertices (degree edges incident) = sumOver edges (edgeSize vertices incident) := by
  exact sumOver_swap vertices edges (fun v e => if incident v e then 1 else 0)

/-- A `p`-uniform incidence relation has total degree `p * number of edges`. -/
theorem sum_degrees_of_uniform (vertices : List α) (edges : List β)
    (incident : α → β → Bool) (p : Nat)
    (uniform : ∀ e ∈ edges, edgeSize vertices incident e = p) :
    sumOver vertices (degree edges incident) = p * edges.length := by
  rw [sum_degrees_eq_sum_edgeSizes]
  exact sumOver_eq_const edges (edgeSize vertices incident) p uniform

/-- Even positive degrees are at least two, giving the support bound. -/
theorem twice_support_le_uniform_edge_count (vertices : List α) (edges : List β)
    (incident : α → β → Bool) (p : Nat)
    (uniform : ∀ e ∈ edges, edgeSize vertices incident e = p)
    (even : ∀ v ∈ vertices, degree edges incident v % 2 = 0) :
    2 * (support vertices edges incident).length ≤ p * edges.length := by
  have h := positive_count_bound vertices (degree edges incident) 2 (by
    intro v hv hpos
    have he := even v hv
    omega)
  rw [sum_degrees_of_uniform vertices edges incident p uniform] at h
  exact h

/-- The generic branching bound needs no parity assumption. -/
theorem four_times_branch_le_uniform_edge_count (vertices : List α) (edges : List β)
    (incident : α → β → Bool) (p : Nat)
    (uniform : ∀ e ∈ edges, edgeSize vertices incident e = p) :
    4 * (branch vertices edges incident).length ≤ p * edges.length := by
  have h := threshold_count_bound vertices (degree edges incident) 4
  rw [sum_degrees_of_uniform vertices edges incident p uniform] at h
  exact h

/-- For ordinary graphs, four times the branching count is at most twice the edge count. -/
theorem sk_branch_bound (vertices : List α) (edges : List β)
    (incident : α → β → Bool)
    (uniform : ∀ e ∈ edges, edgeSize vertices incident e = 2) :
    4 * (branch vertices edges incident).length ≤ 2 * edges.length :=
  four_times_branch_le_uniform_edge_count vertices edges incident 2 uniform

end SpinGlass.Incidence


namespace SpinGlass.Hypergraph

variable {V : Type*} [DecidableEq V]

/-- A simple finite hypergraph has a finite set of finite vertex sets as its edges. -/
abbrev FiniteHypergraph (V : Type*) := Finset (Finset V)

/-- The actual set of vertices used by an edge. -/
def support (Γ : FiniteHypergraph V) : Finset V := Γ.biUnion id

/-- The degree of a vertex is the number of selected edges containing it. -/
def degree (Γ : FiniteHypergraph V) (v : V) : Nat := (Γ.filter (fun e => v ∈ e)).card

/-- The branching set consists of used vertices of degree at least four. -/
def branch (Γ : FiniteHypergraph V) : Finset V := (support Γ).filter (fun v => 4 ≤ degree Γ v)

theorem mem_support_iff {Γ : FiniteHypergraph V} {v : V} :
    v ∈ support Γ ↔ ∃ e ∈ Γ, v ∈ e := by
  simp [support]

theorem degree_pos_of_mem_support {Γ : FiniteHypergraph V} {v : V}
    (hv : v ∈ support Γ) : 0 < degree Γ v := by
  obtain ⟨e, he, hve⟩ := mem_support_iff.mp hv
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩⟩

/-- Direct finite-set handshaking, without an assumed incidence-count identity. -/
theorem sum_degrees (Γ : FiniteHypergraph V) :
    (∑ v ∈ support Γ, degree Γ v) = ∑ e ∈ Γ, e.card := by
  calc
    (∑ v ∈ support Γ, degree Γ v) =
        ∑ e ∈ Γ, ((support Γ).filter (fun v => v ∈ e)).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun (v : V) (e : Finset V) => v ∈ e)
    _ = ∑ e ∈ Γ, e.card := by
      apply Finset.sum_congr rfl
      intro e he
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun hv => ⟨mem_support_iff.mpr ⟨e, he, hv⟩, hv⟩⟩

/-- A direct finite-set bound for any vertices with degree at least `k`. -/
theorem threshold_card_bound (Γ : FiniteHypergraph V) (U : Finset V) (k p : Nat)
    (hk : ∀ v ∈ U, k ≤ degree Γ v)
    (uniform : ∀ e ∈ Γ, e.card = p) :
    k * U.card ≤ p * Γ.card := by
  have h := Finset.card_nsmul_le_card_nsmul (R := Nat)
    (r := fun (v : V) (e : Finset V) => v ∈ e) (s := U) (t := Γ)
    (m := k) (n := p)
    (by
      intro v hv
      exact hk v hv)
    (by
      intro e he
      change (U.filter (fun v => v ∈ e)).card ≤ p
      rw [← uniform e he]
      apply Finset.card_le_card
      intro v hv
      exact (Finset.mem_filter.mp hv).2)
  simpa [nsmul_eq_mul, Nat.mul_comm] using h

/-- The support-size input to the higher-order tail bound, for actual simple hypergraphs. -/
theorem twice_support_le_uniform_edge_count (Γ : FiniteHypergraph V) (p : Nat)
    (uniform : ∀ e ∈ Γ, e.card = p)
    (even : ∀ v ∈ support Γ, degree Γ v % 2 = 0) :
    2 * (support Γ).card ≤ p * Γ.card := by
  apply threshold_card_bound Γ (support Γ) 2 p _ uniform
  intro v hv
  have hpos := degree_pos_of_mem_support hv
  have heven := even v hv
  omega

/-- The branching-size bound for actual finite simple uniform hypergraphs. -/
theorem four_times_branch_le_uniform_edge_count (Γ : FiniteHypergraph V) (p : Nat)
    (uniform : ∀ e ∈ Γ, e.card = p) :
    4 * (branch Γ).card ≤ p * Γ.card := by
  apply threshold_card_bound Γ (branch Γ) 4 p _ uniform
  intro v hv
  exact (Finset.mem_filter.mp hv).2

/-- The SK specialization uses edges of exactly two distinct vertices. -/
theorem sk_branch_bound (Γ : FiniteHypergraph V)
    (uniform : ∀ e ∈ Γ, e.card = 2) :
    4 * (branch Γ).card ≤ 2 * Γ.card :=
  four_times_branch_le_uniform_edge_count Γ 2 uniform

/-- Equivalently, an SK graph needs at least two edges per branching vertex. -/
theorem sk_twice_branch_le_edges (Γ : FiniteHypergraph V)
    (uniform : ∀ e ∈ Γ, e.card = 2) :
    2 * (branch Γ).card ≤ Γ.card := by
  have h := sk_branch_bound Γ uniform
  omega

end SpinGlass.Hypergraph
