import SpinGlass.ColoringRepetitions
import Mathlib.Logic.Equiv.Prod

/-!
# Restricting one global coloring to graph supports

The graph coefficients in the algorithm are correlated because they reuse vertex
colors. These results prove each coefficient's exact moments directly under the
shared global coloring distribution, without assuming independent graphs.
-/

noncomputable section

namespace SpinGlass.ColorRestriction

open scoped BigOperators
open ColoringProbability ColoringRepetitions

/-- Uniform means are preserved by a bijection of finite sample spaces. -/
theorem mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    mean (fun a => f (e a)) = mean f := by
  unfold mean
  rw [Fintype.card_congr e, e.sum_comp]

/-- Ignoring an independent finite coordinate gives the correct uniform marginal. -/
theorem mean_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] (f : A → ℝ) :
    mean (fun p : A × B => f p.1) = mean f := by
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [mean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, mul_inv_rev]
  calc
    (Fintype.card B : ℝ)⁻¹ * (Fintype.card A : ℝ)⁻¹ *
        ((Fintype.card B : ℝ) * ∑ a, f a) =
      (Fintype.card A : ℝ)⁻¹ * ((Fintype.card B : ℝ)⁻¹ * Fintype.card B) * ∑ a, f a := by ring
    _ = _ := by rw [inv_mul_cancel₀ hb]; ring

/-- Restriction to a vertex subset preserves uniform independent coloring. -/
theorem mean_restrict {V Ω : Type*} [Fintype V] [DecidableEq V]
    [Fintype Ω] [Nonempty Ω] (S : Finset V) (f : (S → Ω) → ℝ) :
    mean (fun χ : V → Ω => f (fun v : S => χ v)) = mean f := by
  let e := Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ S) (fun _ => Ω)
  have h := mean_equiv e (fun p => f p.1)
  change mean (fun χ : V → Ω => f (fun v : S => χ v)) =
    mean (fun p : (S → Ω) × ({v : V // v ∉ S} → Ω) => f p.1) at h
  exact h.trans (mean_fst f)

/-- Split every repetition into its used and unused vertex coordinates. -/
def splitRepetitions {V Ω : Type*} [DecidableEq V] (S : Finset V) (R : ℕ) :
    (Fin R → V → Ω) ≃ (Fin R → S → Ω) × (Fin R → {v : V // v ∉ S} → Ω) where
  toFun χ := (fun r v => χ r v, fun r v => χ r v)
  invFun p r v := if h : v ∈ S then p.1 r ⟨v, h⟩ else p.2 r ⟨v, h⟩
  left_inv χ := by
    funext r v
    dsimp
    split <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext r v
      simp
    · funext r v
      simp [v.property]

/-- Arbitrary statistics of all restricted repetitions have the right product law. -/
theorem mean_restrict_repetitions {V Ω : Type*} [Fintype V] [DecidableEq V]
    [Fintype Ω] [Nonempty Ω] (S : Finset V) (R : ℕ) (f : (Fin R → S → Ω) → ℝ) :
    mean (fun χ : Fin R → V → Ω => f (fun r v => χ r v)) = mean f := by
  have h := mean_equiv (splitRepetitions (Ω := Ω) S R) (fun p => f p.1)
  exact h.trans (mean_fst f)

/-- The coefficient for a support set, computed from the common global color array. -/
def supportCoefficient {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (L R : ℕ) (χ : Fin R → V → Fin L) : ℝ :=
  averageCoefficient L R (fun r (v : S) => χ r v)

/-- A shared global coloring gives every support's coefficient mean exactly one. -/
theorem mean_supportCoefficient {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (hS : S.card ≤ L) :
    mean (supportCoefficient S L R) = 1 := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  unfold supportCoefficient
  rw [mean_restrict_repetitions]
  apply mean_averageCoefficient hL hR
  simpa using hS

/-- Exact variance holds even though different supports use overlapping colors. -/
theorem mean_supportCoefficient_variance {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (hS : S.card ≤ L) :
    mean (fun χ : Fin R → V → Fin L => (supportCoefficient S L R χ - 1) ^ 2) =
      (1 - probability L S.card) / ((R : ℝ) * probability L S.card) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  unfold supportCoefficient
  rw [mean_restrict_repetitions S R (fun χ => (averageCoefficient L R χ - 1) ^ 2)]
  simpa using mean_averageCoefficient_variance (V := S) hL hR (by simpa using hS)

/-- The uniform variance bound for support coefficients under shared global colors. -/
theorem mean_supportCoefficient_variance_le {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) {L R : ℕ} (hL : 0 < L) (hR : 0 < R) (hS : S.card ≤ L) :
    mean (fun χ : Fin R → V → Fin L => (supportCoefficient S L R χ - 1) ^ 2) ≤
      Real.exp (L : ℝ) / (R : ℝ) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  unfold supportCoefficient
  rw [mean_restrict_repetitions S R (fun χ => (averageCoefficient L R χ - 1) ^ 2)]
  exact mean_averageCoefficient_variance_le hL hR (by simpa using hS)

end SpinGlass.ColorRestriction
