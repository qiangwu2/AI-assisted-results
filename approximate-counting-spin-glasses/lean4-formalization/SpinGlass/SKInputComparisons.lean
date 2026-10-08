import SpinGlass.FiniteIndexCosts

/-! Prepared SK keys have at most two vertices, so a key comparison has
constant cost even though the prepared array can have order N squared entries. -/
noncomputable section
namespace SpinGlass.SKInputComparisons
open Finset SpinGlass.InputPreparation SpinGlass.FiniteIndexCosts

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem prepared_key_card (beta : ℝ) (J : Finset V → ℝ)
    (x : Finset V × EdgeData) (hx : x ∈ (prepareInput 2 beta J).entries) : x.1.card = 2 := by
  simp only [prepareInput, prepareEdges_entries, List.mem_map, Finset.mem_toList] at hx
  rcases hx with ⟨e,he,hx⟩
  cases hx
  exact (mem_powersetCard.mp he).2

/-- Exact list-lookup implementation: at most eight vertex comparisons per
prepared edge key, including rejected and singleton query keys. -/
theorem prepared_lookup_comparisons (beta : ℝ) (J : Finset V → ℝ)
    (e : Finset V) (he : e.card ≤ 2) :
    (lookup e (prepareInput 2 beta J).entries).2 ≤ 8 * (Fintype.card V)^2 := by
  have h := lookup_comparisons e (prepareInput 2 beta J).entries he
    (fun x hx => (prepared_key_card beta J x hx).le)
  have hc : (Fintype.card V).choose 2 ≤ (Fintype.card V)^2 := Nat.choose_le_pow _ _
  simp only [prepareInput, prepareEdges_entries, List.length_map, length_toList,
    card_powersetCard, card_univ] at h
  norm_num at h
  simpa only [prepareInput, prepareEdges_entries, scaleComputation_value] using
    h.trans (Nat.mul_le_mul_left 8 hc)

/-- Every physical endpoint-pair query satisfies the constant-size key bound. -/
theorem pair_lookup_comparisons (beta : ℝ) (J : Finset V → ℝ) (a b : V) :
    (lookup ({a,b} : Finset V) (prepareInput 2 beta J).entries).2 ≤ 8 * (Fintype.card V)^2 :=
  prepared_lookup_comparisons beta J _ (by by_cases h : a=b <;> simp [h])

end SpinGlass.SKInputComparisons
