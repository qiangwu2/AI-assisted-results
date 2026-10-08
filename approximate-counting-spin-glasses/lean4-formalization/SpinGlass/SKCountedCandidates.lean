import SpinGlass.SKReferenceAggregation

/-! Bounded-cardinality enumeration of candidate branch sets. -/
noncomputable section
namespace SpinGlass.SKCountedExecution
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Enumerate only the requested cardinalities, and unite the disjoint families.
This definition does not scan the full powerset. -/
def candidates (V : Type*) [Fintype V] [DecidableEq V] (D : ℕ) : Finset (Finset V) :=
  (Finset.range (min D (Fintype.card V) + 1)).biUnion
    (fun b => (Finset.univ : Finset V).powersetCard b)

@[simp] theorem mem_candidates (D : ℕ) (A : Finset V) :
    A ∈ candidates V D ↔ A.card ≤ D := by
  simp only [candidates, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨b, hb, rfl⟩
    omega
  · intro h
    exact ⟨A.card, by have := Finset.card_le_univ A; omega, rfl⟩

theorem candidates_eq_filter (D : ℕ) :
    candidates V D = (Finset.univ : Finset V).powerset.filter (fun A => A.card ≤ D) := by
  ext A
  simp

/-- Any scalar sum over the executed candidate enumeration equals the displayed
nested cardinality enumeration in Algorithm 2. -/
theorem sum_candidates {M : Type*} [AddCommMonoid M] (D : ℕ) (f : Finset V → M) :
    (∑ A ∈ candidates V D, f A) =
      ∑ b ∈ Finset.range (D + 1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b, f A := by
  rw [candidates_eq_filter]
  symm
  have h := Finset.sum_fiberwise_eq_sum_filter ((Finset.univ : Finset V).powerset)
    (Finset.range (D + 1)) Finset.card f
  simpa only [← Finset.powersetCard_eq_filter, Finset.mem_range, Nat.lt_succ_iff] using h

theorem sum_candidates_card (D : ℕ) (f : ℕ → ℕ) :
    (∑ A ∈ candidates V D, f A.card) =
      ∑ b ∈ Finset.range (D + 1), (Fintype.card V).choose b * f b := by
  rw [sum_candidates]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [Finset.sum_congr rfl (fun A hA => congrArg f (Finset.mem_powersetCard.mp hA).2)]
  simp

end SpinGlass.SKCountedExecution
