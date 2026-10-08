import SpinGlass.SKActualEvaluator
import SpinGlass.SKTraversalPrimitives

/-! # Actual primitive graph monomials in the evaluator's coordinates -/
noncomputable section
namespace SpinGlass.SKPrimitiveMonomials
open scoped BigOperators
open SKGraphMonomial SKRing SKFastEvaluator SKActualEvaluator SKTraversal
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The four actual graph coordinates determine the precise inserted monomial. -/
theorem value_of_coordinates {b L : ℕ} (A : Finset V) (branch : Fin b → V)
    (χ : V → Fin L) (f : Finset V → ℝ) (Γ : Finset (Finset V))
    (k : ℕ) (S : Finset (Fin L)) (d : Fin b → CappedDegree)
    (hk : Γ.card = k) (hS : colors id A χ Γ = S) (hc : Colorful id A χ Γ)
    (hd : (fun a => CappedDegree.ofNat (Expansion.degree id Γ (branch a))) = d) :
    value id A branch χ f Γ = insertMonomial k S d (∏ e ∈ Γ, f e) := by
  unfold value insertMonomial
  simp only [hk, if_pos hc]
  split
  · congr 1
    apply Prod.ext
    · exact Fin.ext hk
    · exact Prod.ext hS hd
  · rfl

/-- All coefficients at one fixed basis position combine by ordinary addition. -/
theorem insertMonomial_sum {b L : ℕ} {I : Type*} (F : Finset I)
    (k : ℕ) (S : Finset (Fin L)) (d : Fin b → CappedDegree) (g : I → ℝ) :
    insertMonomial k S d (∑ i ∈ F, g i) = ∑ i ∈ F, insertMonomial k S d (g i) := by
  classical
  by_cases hk : k ≤ L
  · simp only [insertMonomial, dif_pos hk]
    apply SKRing.ext
    rw [coeff_sum]
    funext z
    simp [monomial, SKCoefficient.single, Finset.sum_apply, Finset.sum_ite_irrel]
  · simp [insertMonomial, hk]

/-- Reduced branch degrees of a literal path coincide with equation (66). -/
theorem between_degrees (A : Finset V) (a c : Fin A.card) (hac : a ≠ c)
    (l : List V) (hl : l.Nodup) (hout : ∀ v ∈ l, v ∉ A) :
    (fun d => CappedDegree.ofNat
      (Expansion.degree id (betweenEdges (branch A a) (branch A c) l) (branch A d))) =
      pathDegrees a c := by
  have hav : branch A a ≠ branch A c := fun h => hac (branch_injective A h)
  have hbr : ∀ d, branch A d ∉ l := fun d h => hout _ h (branch_mem A d)
  funext d
  rw [betweenEdges_degree hav hl (hbr a) (hbr c)]
  have heqa : branch A d = branch A a ↔ d = a := (branch_injective A).eq_iff
  have heqc : branch A d = branch A c ↔ d = c := (branch_injective A).eq_iff
  simp only [heqa, heqc, hbr d, if_false, pathDegrees]
  by_cases hda : d = a
  · subst d; simp [hac]
  · by_cases hdc : d = c
    · subst d; simp [Ne.symm hac]
    · simp [hda, hdc]

/-- Rooted returns increment exactly their actual root by two. -/
theorem return_degrees (A : Finset V) (a : Fin A.card)
    (l : List V) (hl : l.Nodup) (hout : ∀ v ∈ l, v ∉ A) (hlen : 2 ≤ l.length) :
    (fun d => CappedDegree.ofNat
      (Expansion.degree id (rootedEdges (branch A a) l) (branch A d))) =
      pathDegrees a a := by
  have hbr : ∀ d, branch A d ∉ l := fun d h => hout _ h (branch_mem A d)
  funext d
  rw [rootedEdges_degree hl (hbr a) hlen]
  have heqa : branch A d = branch A a ↔ d = a := (branch_injective A).eq_iff
  simp only [heqa, hbr d, or_false, pathDegrees]
  by_cases hda : d = a <;> simp [hda]

/-- An entirely outside cycle has no branch degree contribution. -/
theorem cycle_degrees (A : Finset V) (l : List V) (hl : l.Nodup)
    (hout : ∀ v ∈ l, v ∉ A) (hlen : 3 ≤ l.length) :
    (fun d : Fin A.card => CappedDegree.ofNat
      (Expansion.degree id (cycleEdges l) (branch A d))) = (fun _ => 0) := by
  funext d
  have hbr : branch A d ∉ l := fun h => hout _ h (branch_mem A d)
  simp only [cycleEdges_degree hl hlen, hbr, if_false]
  rfl

/-- The direct branch factor is the actual singleton-edge graph monomial. -/
theorem direct_value {L : ℕ} (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset V → ℝ) (a c : Fin A.card) (hac : a ≠ c) :
    value id A (branch A) (totalColor A χ hL) f {{branch A a, branch A c}} =
      direct (L := L) (branch A) f a c := by
  have hout : outside id A ({{branch A a,branch A c}} : Finset (Finset V)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvU,hvA⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hvU
    have heq : e = {branch A a,branch A c} := Finset.mem_singleton.mp he
    simp only [id_eq, heq, Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | rfl <;> exact hvA (branch_mem A _)
  have hc : Colorful id A (totalColor A χ hL) ({{branch A a,branch A c}} : Finset (Finset V)) := by
    rw [Colorful, hout]
    simpa using Set.injOn_empty (totalColor A χ hL)
  have hd := between_degrees A a c hac [] (by simp) (by simp)
  have he : betweenEdges (branch A a) (branch A c) [] = {{branch A a,branch A c}} := by
    simp [betweenEdges, pathEdges, Finset.pair_comm]
  rw [he] at hd
  have ht := value_of_coordinates A (branch A) (totalColor A χ hL) f
    {{branch A a,branch A c}} 1 ∅ (pathDegrees a c) (by simp)
    (by simp [colors, hout]) hc hd
  simpa [direct, pairWeight] using ht

end SpinGlass.SKPrimitiveMonomials
