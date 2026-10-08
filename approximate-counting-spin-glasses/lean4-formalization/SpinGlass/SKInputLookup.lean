import SpinGlass.FiniteIndexCosts

/-! Literal prepared-edge lookup comparisons for the SK tables, including
diagonal queries whose key has only one vertex. -/
noncomputable section
namespace SpinGlass.SKInputLookup
open SpinGlass.InputPreparation SpinGlass.FiniteIndexCosts
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem prepared_key_card (beta : ℝ) (J : Finset V → ℝ)
    {x : Finset V × EdgeData} (hx : x∈(prepareInput 2 beta J).entries) : x.1.card=2 := by
  simp only [prepareInput,prepareEdges_entries,List.mem_map,Finset.mem_toList] at hx
  obtain ⟨e,he,rfl⟩ := hx
  exact (Finset.mem_powersetCard.mp he).2

theorem prepared_lookup_eight (beta : ℝ) (J : Finset V → ℝ) (i j : V) :
    (lookup {i,j} (prepareInput 2 beta J).entries).2 ≤
      8*(prepareInput 2 beta J).entries.length := by
  have h := lookup_comparisons (N := 2) {i,j} (prepareInput 2 beta J).entries
    (by by_cases h : i=j <;> simp [h,Finset.card_pair]) (fun x hx => (prepared_key_card beta J hx).le)
  norm_num at h
  exact h

theorem prepared_lookup_eight_visits (beta : ℝ) (J : Finset V → ℝ) (i j : V) :
    (lookup {i,j} (prepareInput 2 beta J).entries).2 ≤
      8*lookupVisits {i,j} (prepareInput 2 beta J).entries := by
  have h := lookup_comparisons_visits (N := 2) {i,j} (prepareInput 2 beta J).entries
    (by by_cases h : i=j <;> simp [h,Finset.card_pair]) (fun x hx => (prepared_key_card beta J hx).le)
  norm_num at h
  exact h

theorem prepared_lookup_quadratic (beta : ℝ) (J : Finset V → ℝ) (i j : V) :
    (lookup {i,j} (prepareInput 2 beta J).entries).2 ≤ 4*(Fintype.card V)^2 := by
  have h := prepared_lookup_eight beta J i j
  have hlen : (prepareInput 2 beta J).entries.length = (Fintype.card V).choose 2 := by
    simp [prepareInput]
  rw [hlen] at h
  apply h.trans
  have hc : (Fintype.card V)*(Fintype.card V-1) ≤ (Fintype.card V)^2 := by
    nlinarith [Nat.sub_le (Fintype.card V) 1]
  rw [Nat.choose_two_right]
  have hd := Nat.div_mul_le_self ((Fintype.card V)*(Fintype.card V-1)) 2
  omega

end SpinGlass.SKInputLookup
