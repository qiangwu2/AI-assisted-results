import SpinGlass.SKPrimitiveExpansion
import SpinGlass.SKComponents

/-!
# Concrete graph monomials and coefficient extraction

The graph encoding records the actual number of distinct edges, outside color
set, signed edge-weight product, and reduced degree at each specified branch
vertex. Multiplication agrees with disjoint graph union and rejects color reuse.
-/

noncomputable section
namespace SpinGlass.SKGraphMonomial

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open SKRing

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- The outside vertex support of an actual edge family. -/
def outside (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) : Finset V :=
  Γ.biUnion incidence \ A

/-- Outside colors, each represented once in the square-zero algebra. -/
def colors {L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (χ : V → Fin L) (Γ : Finset E) : Finset (Fin L) :=
  (outside incidence A Γ).image χ

/-- The edge family uses no outside color more than once. -/
def Colorful {L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (χ : V → Fin L) (Γ : Finset E) : Prop :=
  Set.InjOn χ (outside incidence A Γ)

/-- Actual reduced graph coordinate; the edge bound is the algebra's t cutoff. -/
def basis {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (Γ : Finset E) (hΓ : Γ.card ≤ L) :
    SKCoefficient.Basis b L :=
  (⟨Γ.card, Nat.lt_succ_of_le hΓ⟩, colors incidence A χ Γ,
    fun a => CappedDegree.ofNat (Expansion.degree incidence Γ (branch a)))

/-- Signed graph weight is the product over its distinct edges. -/
def weight (w : E → ℝ) (Γ : Finset E) : ℝ := ∏ e ∈ Γ, w e

/-- The graph monomial, including annihilation by budget or repeated color. -/
def value {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (Γ : Finset E) : Element b L := by
  classical
  exact if hΓ : Γ.card ≤ L then
    if Colorful incidence A χ Γ then monomial (basis incidence A branch χ Γ hΓ) (weight w Γ)
    else 0
  else 0

@[simp] theorem outside_union (incidence : E → Finset V) (A : Finset V) (Γ Δ : Finset E) :
    outside incidence A (Γ ∪ Δ) = outside incidence A Γ ∪ outside incidence A Δ := by
  ext v
  simp only [outside, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨⟨e, he | he, hv⟩, ha⟩
    · exact Or.inl ⟨⟨e, he, hv⟩, ha⟩
    · exact Or.inr ⟨⟨e, he, hv⟩, ha⟩
  · rintro (⟨⟨e, he, hv⟩, ha⟩ | ⟨⟨e, he, hv⟩, ha⟩)
    · exact ⟨⟨e, Or.inl he, hv⟩, ha⟩
    · exact ⟨⟨e, Or.inr he, hv⟩, ha⟩

@[simp] theorem colors_union {L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (χ : V → Fin L) (Γ Δ : Finset E) :
    colors incidence A χ (Γ ∪ Δ) = colors incidence A χ Γ ∪ colors incidence A χ Δ := by
  simp [colors, Finset.image_union]

/-- Distinct edge families add actual incidence degrees, including at branches. -/
theorem degree_union (incidence : E → Finset V) (Γ Δ : Finset E)
    (hd : Disjoint Γ Δ) (v : V) :
    Expansion.degree incidence (Γ ∪ Δ) v =
      Expansion.degree incidence Γ v + Expansion.degree incidence Δ v := by
  simp only [Expansion.degree, Finset.filter_union]
  exact Finset.card_union_of_disjoint (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

theorem weight_union (w : E → ℝ) (Γ Δ : Finset E) (hd : Disjoint Γ Δ) :
    weight w (Γ ∪ Δ) = weight w Γ * weight w Δ := Finset.prod_union hd

/-- Colorfulness of disjoint outside supports is exactly internal and cross compatibility. -/
theorem colorful_union_iff {L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (χ : V → Fin L) (Γ Δ : Finset E)
    (hd : Disjoint (outside incidence A Γ) (outside incidence A Δ)) :
    Colorful incidence A χ (Γ ∪ Δ) ↔ Colorful incidence A χ Γ ∧
      Colorful incidence A χ Δ ∧ Disjoint (colors incidence A χ Γ) (colors incidence A χ Δ) := by
  classical
  unfold Colorful
  rw [outside_union, Finset.coe_union, Set.injOn_union (by exact_mod_cast hd)]
  simp only [colors, Finset.disjoint_left, Finset.mem_image]
  constructor
  · rintro ⟨hΓ, hΔ, hcross⟩
    refine ⟨hΓ, hΔ, ?_⟩
    rintro c ⟨v, hv, rfl⟩ ⟨u, hu, heq⟩
    exact hcross v hv u hu heq.symm
  · rintro ⟨hΓ, hΔ, hcross⟩
    refine ⟨hΓ, hΔ, ?_⟩
    intro v hv u hu heq
    exact hcross ⟨v, hv, rfl⟩ ⟨u, hu, heq.symm⟩

/-- Surviving multiplication records the union's exact graph coordinate. -/
theorem combine_basis {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (Γ Δ : Finset E)
    (hd : Disjoint Γ Δ) (hΓ : Γ.card ≤ L) (hΔ : Δ.card ≤ L)
    (h : SKCoefficient.compatible (basis incidence A branch χ Γ hΓ)
      (basis incidence A branch χ Δ hΔ)) :
    SKCoefficient.combine (basis incidence A branch χ Γ hΓ)
      (basis incidence A branch χ Δ hΔ) h =
    basis incidence A branch χ (Γ ∪ Δ)
      (by rw [Finset.card_union_of_disjoint hd]; exact h.1) := by
  apply Prod.ext
  · apply Fin.ext
    exact (Finset.card_union_of_disjoint hd).symm
  · apply Prod.ext
    · exact (colors_union incidence A χ Γ Δ).symm
    · funext a
      exact (CappedDegree.ofNat_add _ _).symm.trans
        (congrArg CappedDegree.ofNat (degree_union incidence Γ Δ hd (branch a)).symm)

/-- Actual disjoint edge/outside-vertex union is exactly algebra multiplication.
No colorfulness assumption is needed: collisions are annihilated on both sides. -/
theorem value_mul {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (Γ Δ : Finset E)
    (he : Disjoint Γ Δ)
    (hv : Disjoint (outside incidence A Γ) (outside incidence A Δ)) :
    value incidence A branch χ w Γ * value incidence A branch χ w Δ =
      value incidence A branch χ w (Γ ∪ Δ) := by
  classical
  have hcard := Finset.card_union_of_disjoint he
  have hcolor := colorful_union_iff incidence A χ Γ Δ hv
  by_cases hΓ : Γ.card ≤ L
  · by_cases hΔ : Δ.card ≤ L
    · by_cases hcΓ : Colorful incidence A χ Γ
      · by_cases hcΔ : Colorful incidence A χ Δ
        · by_cases ht : (Γ ∪ Δ).card ≤ L
          · by_cases hc : Disjoint (colors incidence A χ Γ) (colors incidence A χ Δ)
            · have hcomp : SKCoefficient.compatible (basis incidence A branch χ Γ hΓ)
                  (basis incidence A branch χ Δ hΔ) := ⟨by simpa [basis, hcard] using ht, hc⟩
              have hcu := hcolor.mpr ⟨hcΓ, hcΔ, hc⟩
              simp only [value, dif_pos hΓ, dif_pos hΔ, if_pos hcΓ, if_pos hcΔ,
                dif_pos ht, if_pos hcu]
              apply ext
              change SKCoefficient.mul (SKCoefficient.single _ _) (SKCoefficient.single _ _) =
                SKCoefficient.single _ _
              rw [SKCoefficient.mul_single_single_accepted _ _ _ _ hcomp,
                combine_basis incidence A branch χ Γ Δ he hΓ hΔ hcomp,
                weight_union w Γ Δ he]
            · have hcu : ¬ Colorful incidence A χ (Γ ∪ Δ) := fun h => hc (hcolor.mp h).2.2
              simp only [value, dif_pos hΓ, dif_pos hΔ, if_pos hcΓ, if_pos hcΔ,
                dif_pos ht, if_neg hcu]
              apply ext
              apply SKCoefficient.mul_single_single_rejected
              exact fun h => hc h.2
          · simp only [value, dif_pos hΓ, dif_pos hΔ, if_pos hcΓ, if_pos hcΔ, dif_neg ht]
            apply ext
            apply SKCoefficient.mul_single_single_rejected
            intro h
            exact ht (by simpa [basis, hcard] using h.1)
        · have hcu : ¬ Colorful incidence A χ (Γ ∪ Δ) := fun h => hcΔ (hcolor.mp h).2.1
          simp [value, hΓ, hΔ, hcΔ, hcu]
      · have hcu : ¬ Colorful incidence A χ (Γ ∪ Δ) := fun h => hcΓ (hcolor.mp h).1
        simp [value, hΓ, hΔ, hcΓ, hcu]
    · have ht : ¬ (Γ ∪ Δ).card ≤ L := by omega
      simp [value, hΔ, ht]
  · have ht : ¬ (Γ ∪ Δ).card ≤ L := by omega
    simp [value, hΓ, ht]

/-- Extraction coordinate in equation (75). -/
def target {b L : ℕ} (k : Fin (L + 1)) (S : Finset (Fin L)) : SKCoefficient.Basis b L :=
  (k, S, fun _ => CappedDegree.ofNat 4)

/-- The unreduced branch degrees accepted by coefficient extraction. -/
def Accepts {b : ℕ} (incidence : E → Finset V) (branch : Fin b → V) (Γ : Finset E) : Prop :=
  ∀ a, 4 ≤ Expansion.degree incidence Γ (branch a) ∧
    Expansion.degree incidence Γ (branch a) % 2 = 0

/-- Matching a reduced graph coordinate is precisely the stated graph predicate. -/
theorem basis_eq_target_iff {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (Γ : Finset E) (hΓ : Γ.card ≤ L)
    (k : Fin (L + 1)) (S : Finset (Fin L)) :
    basis incidence A branch χ Γ hΓ = target k S ↔
      Γ.card = k.val ∧ colors incidence A χ Γ = S ∧ Accepts incidence branch Γ := by
  constructor
  · intro h
    refine ⟨congrArg (fun z => z.1.val) h, congrArg (fun z => z.2.1) h, ?_⟩
    intro a
    apply (rho_eq_four_iff _).mp
    have he := congrArg (fun z => (z.2.2 a).val) h
    simpa [basis, target, CappedDegree.val_ofNat] using he
  · rintro ⟨hk, hS, hd⟩
    apply Prod.ext
    · exact Fin.ext hk
    · apply Prod.ext hS
      funext a
      apply CappedDegree.ext_val
      change rho _ = rho 4
      rw [rho_four]
      exact (rho_eq_four_iff _).mpr (hd a)

/-- One graph contributes its signed weight precisely to its accepted coordinate. -/
theorem value_coefficient {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (Γ : Finset E)
    (k : Fin (L + 1)) (S : Finset (Fin L)) :
    (value incidence A branch χ w Γ).coeff (target k S) =
      if Γ.card = k.val ∧ colors incidence A χ Γ = S ∧
        Colorful incidence A χ Γ ∧ Accepts incidence branch Γ then weight w Γ else 0 := by
  classical
  by_cases hΓ : Γ.card ≤ L
  · by_cases hc : Colorful incidence A χ Γ
    · simp [value, hΓ, hc, monomial, SKCoefficient.single, basis_eq_target_iff]
    · simp [value, hΓ, hc]
  · have hk : Γ.card ≠ k.val := by have := k.isLt; omega
    simp [value, hΓ, hk]

/-- With degree zero or two outside the candidate set, extraction accepts exactly
an even graph whose actual branching set is the candidate set. -/
theorem accepts_iff_even_branch {b : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (Γ : Finset E)
    (hbranch : ∀ v, v ∈ A ↔ ∃ a, branch a = v)
    (hout : ∀ v, v ∉ A → Expansion.degree incidence Γ v = 0 ∨
      Expansion.degree incidence Γ v = 2) :
    Accepts incidence branch Γ ↔
      Expansion.IsEven incidence Γ ∧ SKComponents.branchVertices incidence Γ = A := by
  constructor
  · intro h
    constructor
    · intro v
      by_cases hv : v ∈ A
      · obtain ⟨a, rfl⟩ := (hbranch v).mp hv
        exact Nat.even_iff.mpr (h a).2
      · rcases hout v hv with h0 | h2
        · simp [h0]
        · simp [h2]
    · ext v
      simp only [SKComponents.branchVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hd
        by_contra hv
        rcases hout v hv with h0 | h2 <;> omega
      · intro hv
        obtain ⟨a, rfl⟩ := (hbranch v).mp hv
        exact (h a).1
  · rintro ⟨heven, hset⟩ a
    have hv : branch a ∈ SKComponents.branchVertices incidence Γ := by
      rw [hset]
      exact (hbranch _).mpr ⟨a, rfl⟩
    exact ⟨(Finset.mem_filter.mp hv).2, Nat.even_iff.mp (heven (branch a))⟩

end SpinGlass.SKGraphMonomial
