import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Finite graphical expansion

Boolean coordinates encode independent uniform Ising spins.  Edges are an arbitrary
finite indexed family of finite vertex sets; uniformity, distinctness of different
indices, and a restriction on the number of vertices are not needed for this identity.
The even-degree constraint below is an actual combinatorial condition, not an
assumption about the spin sum.
-/

noncomputable section

namespace SpinGlass.Expansion

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- The Boolean encoding of an Ising spin. -/
def spinSign (b : Bool) : ℝ := if b then -1 else 1

/-- The product of spins on an interaction. -/
def edgeCharacter (incidence : E → Finset V) (σ : V → Bool) (e : E) : ℝ :=
  ∏ v ∈ incidence e, spinSign (σ v)

/-- A Fourier character of the Boolean cube, indexed by its vertex support. -/
def spinCharacter (S : Finset V) (σ : V → Bool) : ℝ :=
  ∏ v ∈ S, spinSign (σ v)

/-- Degree in a selected finite family of hyperedges. -/
def degree (incidence : E → Finset V) (Γ : Finset E) (v : V) : ℕ :=
  (Γ.filter (fun e => v ∈ incidence e)).card

/-- Every vertex, including unused vertices of degree zero, has even degree. -/
def IsEven (incidence : E → Finset V) (Γ : Finset E) : Prop :=
  ∀ v, Even (degree incidence Γ v)

instance (incidence : E → Finset V) (Γ : Finset E) :
    Decidable (IsEven incidence Γ) := inferInstanceAs (Decidable (∀ v : V, Even (degree incidence Γ v)))

/-- Expectation with respect to all independent uniform Boolean spin coordinates. -/
def spinMean (f : (V → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ Fintype.card V)⁻¹ * ∑ σ, f σ

@[simp] theorem abs_spinSign (b : Bool) : |spinSign b| = 1 := by
  cases b <;> norm_num [spinSign]

@[simp] theorem spinSign_sq (b : Bool) : spinSign b ^ 2 = 1 := by
  cases b <;> norm_num [spinSign]

/-- Averaging one coordinate detects parity. -/
theorem sum_spinSign_pow (n : ℕ) :
    (∑ b : Bool, spinSign b ^ n) = if Even n then (2 : ℝ) else 0 := by
  rcases Nat.even_or_odd n with h | h
  · simp [spinSign, h, h.neg_one_pow]
  · simp [spinSign, (Nat.not_even_iff_odd.mpr h), h.neg_one_pow]

/-- Regrouping all edge-spin factors by vertex gives the degree powers. -/
theorem character_eq_degree (incidence : E → Finset V) (Γ : Finset E)
    (σ : V → Bool) :
    (∏ e ∈ Γ, edgeCharacter incidence σ e) =
      ∏ v, spinSign (σ v) ^ degree incidence Γ v := by
  classical
  calc
    (∏ e ∈ Γ, edgeCharacter incidence σ e) =
        ∏ e ∈ Γ, ∏ v : V, if v ∈ incidence e then spinSign (σ v) else 1 := by
      apply Finset.prod_congr rfl
      intro e he
      simp [edgeCharacter]
    _ = ∏ v : V, ∏ e ∈ Γ, if v ∈ incidence e then spinSign (σ v) else 1 := by
      rw [Finset.prod_comm]
    _ = ∏ v, spinSign (σ v) ^ degree incidence Γ v := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [← Finset.prod_filter]
      simp [degree]

/-- Unnormalized orthogonality of spin characters. -/
theorem sum_character (incidence : E → Finset V) (Γ : Finset E) :
    (∑ σ : V → Bool, ∏ e ∈ Γ, edgeCharacter incidence σ e) =
      if IsEven incidence Γ then (2 : ℝ) ^ Fintype.card V else 0 := by
  classical
  simp_rw [character_eq_degree]
  rw [← Fintype.prod_sum (fun v (b : Bool) => spinSign b ^ degree incidence Γ v)]
  simp_rw [sum_spinSign_pow]
  by_cases h : IsEven incidence Γ
  · have hv : ∀ v, Even (degree incidence Γ v) := h
    simp [h, hv]
  · rw [if_neg h]
    obtain ⟨v, hv⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv]

/-- A spin monomial has mean one exactly for even hypergraphs, and zero otherwise. -/
theorem mean_character (incidence : E → Finset V) (Γ : Finset E) :
    spinMean (fun σ : V → Bool => ∏ e ∈ Γ, edgeCharacter incidence σ e) =
      if IsEven incidence Γ then (1 : ℝ) else 0 := by
  classical
  rw [spinMean, sum_character]
  split_ifs <;> simp

/-- The exact finite high-temperature graphical expansion before normalization. -/
theorem graphical_expansion_sum (incidence : E → Finset V) (edges : Finset E)
    (w : E → ℝ) :
    (∑ σ : V → Bool, ∏ e ∈ edges, (1 + w e * edgeCharacter incidence σ e)) =
      (2 : ℝ) ^ Fintype.card V *
        ∑ Γ ∈ edges.powerset.filter (IsEven incidence), ∏ e ∈ Γ, w e := by
  classical
  simp_rw [Finset.prod_one_add]
  rw [Finset.sum_comm]
  simp_rw [Finset.prod_mul_distrib, ← Finset.mul_sum, sum_character]
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases h : IsEven incidence Γ <;> simp [h, mul_comm]

/-- The even-hypergraph expansion for arbitrary finite real edge weights. -/
theorem graphical_expansion (incidence : E → Finset V) (edges : Finset E)
    (w : E → ℝ) :
    spinMean (fun σ : V → Bool =>
      ∏ e ∈ edges, (1 + w e * edgeCharacter incidence σ e)) =
      ∑ Γ ∈ edges.powerset.filter (IsEven incidence), ∏ e ∈ Γ, w e := by
  rw [spinMean, graphical_expansion_sum, ← mul_assoc]
  simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem abs_edgeCharacter (incidence : E → Finset V) (σ : V → Bool)
    (e : E) : |edgeCharacter incidence σ e| = 1 := by
  simp [edgeCharacter, Finset.abs_prod]

/-- The graphical sum is positive whenever every absolute edge weight is below one. -/
theorem graphical_sum_pos (incidence : E → Finset V) (edges : Finset E)
    (w : E → ℝ) (hw : ∀ e ∈ edges, |w e| < 1) :
    0 < ∑ Γ ∈ edges.powerset.filter (IsEven incidence), ∏ e ∈ Γ, w e := by
  classical
  rw [← graphical_expansion incidence edges w, spinMean]
  apply mul_pos
  · exact inv_pos.mpr (pow_pos (by norm_num) _)
  · apply Finset.sum_pos
    · intro σ hσ
      apply Finset.prod_pos
      intro e he
      have habs : |w e * edgeCharacter incidence σ e| < 1 := by
        simpa only [abs_mul, abs_edgeCharacter, mul_one] using hw e he
      have hneg := (abs_lt.mp habs).1
      linarith
    · exact Finset.univ_nonempty

/-- The paper's p-uniform model is the specialization to p-element vertex sets. -/
theorem pure_p_spin_expansion (N p : ℕ) (w : Finset (Fin N) → ℝ) :
    spinMean (fun σ : Fin N → Bool =>
      ∏ e ∈ (Finset.univ : Finset (Fin N)).powersetCard p,
        (1 + w e * edgeCharacter id σ e)) =
      ∑ Γ ∈ ((Finset.univ : Finset (Fin N)).powersetCard p).powerset.filter
          (IsEven id), ∏ e ∈ Γ, w e := by
  exact graphical_expansion id _ w

/-- Finite spin averages commute with finite sums. -/
theorem spinMean_sum {I : Type*} (s : Finset I) (f : I → (V → Bool) → ℝ) :
    spinMean (fun σ => ∑ i ∈ s, f i σ) = ∑ i ∈ s, spinMean (f i) := by
  classical
  unfold spinMean
  rw [Finset.sum_comm, Finset.mul_sum]

/-- A constant coefficient factors out of a spin average. -/
theorem spinMean_mul_left (a : ℝ) (f : (V → Bool) → ℝ) :
    spinMean (fun σ => a * f σ) = a * spinMean f := by
  unfold spinMean
  rw [← Finset.mul_sum]
  ring

omit [Fintype V] in
private theorem even_pair_iff (S T : Finset V) :
    IsEven (fun b : Bool => if b then T else S) {false, true} ↔ S = T := by
  classical
  constructor
  · intro h
    ext v
    have hv := h v
    by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;>
      simp [degree, Finset.filter_insert, Finset.filter_singleton, hs, ht] at hv ⊢
  · rintro rfl v
    by_cases hs : v ∈ S <;> simp [degree, Finset.filter_insert, Finset.filter_singleton, hs]

/-- Different Boolean-cube characters are orthogonal under independent uniform signs. -/
theorem character_orthogonality (S T : Finset V) :
    spinMean (fun σ : V → Bool => spinCharacter S σ * spinCharacter T σ) =
      if S = T then (1 : ℝ) else 0 := by
  classical
  have h := mean_character (fun b : Bool => if b then T else S) {false, true}
  simp only [even_pair_iff] at h
  simpa [edgeCharacter, spinCharacter] using h

/-- The exact second moment of any finite sign polynomial is its squared coefficient sum. -/
theorem polynomial_second_moment (A : Finset (Finset V)) (c : Finset V → ℝ) :
    spinMean (fun σ : V → Bool => (∑ S ∈ A, c S * spinCharacter S σ) ^ 2) =
      ∑ S ∈ A, c S ^ 2 := by
  classical
  calc
    spinMean (fun σ : V → Bool => (∑ S ∈ A, c S * spinCharacter S σ) ^ 2) =
        spinMean (fun σ => ∑ S ∈ A, ∑ T ∈ A,
          (c S * c T) * (spinCharacter S σ * spinCharacter T σ)) := by
      congr 1
      funext σ
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      ring
    _ = ∑ S ∈ A, ∑ T ∈ A, (c S * c T) * if S = T then 1 else 0 := by
      simp_rw [spinMean_sum, spinMean_mul_left, character_orthogonality]
    _ = ∑ S ∈ A, c S ^ 2 := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [mul_ite, hS, sq]

/-- For arbitrary retained or discarded graph families, independent edge signs eliminate
all cross terms; the remaining terms are products of squared edge magnitudes. -/
theorem edge_subset_second_moment (graphs : Finset (Finset V)) (a : V → ℝ) :
    spinMean (fun η : V → Bool =>
      (∑ Γ ∈ graphs, ∏ e ∈ Γ, (a e * spinSign (η e))) ^ 2) =
      ∑ Γ ∈ graphs, ∏ e ∈ Γ, a e ^ 2 := by
  simpa [Finset.prod_mul_distrib, spinCharacter, Finset.prod_pow] using
    polynomial_second_moment graphs (fun Γ => ∏ e ∈ Γ, a e)

/-- Only the empty character has nonzero uniform mean. -/
theorem mean_spinCharacter (S : Finset V) :
    spinMean (spinCharacter S) = if S = ∅ then (1 : ℝ) else 0 := by
  change spinMean (fun σ : V → Bool => ∏ v ∈ S, spinSign (σ v)) = _
  simpa [spinCharacter] using character_orthogonality S ∅

/-- Independent signs annihilate every nonempty graph monomial. -/
theorem edge_subset_mean (graphs : Finset (Finset V)) (a : V → ℝ) :
    spinMean (fun η : V → Bool =>
      ∑ Γ ∈ graphs, ∏ e ∈ Γ, (a e * spinSign (η e))) =
      if ∅ ∈ graphs then (1 : ℝ) else 0 := by
  classical
  simp_rw [Finset.prod_mul_distrib]
  change spinMean (fun η => ∑ Γ ∈ graphs,
    (∏ e ∈ Γ, a e) * spinCharacter Γ η) = _
  simp_rw [spinMean_sum, spinMean_mul_left, mean_spinCharacter]
  simp [mul_ite]

end SpinGlass.Expansion

#print axioms SpinGlass.Expansion.mean_character
#print axioms SpinGlass.Expansion.graphical_expansion

#print axioms SpinGlass.Expansion.graphical_sum_pos
#print axioms SpinGlass.Expansion.pure_p_spin_expansion

#print axioms SpinGlass.Expansion.character_orthogonality
#print axioms SpinGlass.Expansion.polynomial_second_moment
#print axioms SpinGlass.Expansion.edge_subset_second_moment
#print axioms SpinGlass.Expansion.edge_subset_mean
