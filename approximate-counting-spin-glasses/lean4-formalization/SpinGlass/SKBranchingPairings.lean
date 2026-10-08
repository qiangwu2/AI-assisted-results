import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Distinguished-half-edge pairings

A pairing is an actual fixed-point-free involutive permutation of the finite
half-edge set. Its cardinality bound is derived from mathlib's proved permutation
cycle-type count, rather than assuming the usual double-factorial count.
-/
noncomputable section
namespace SpinGlass.SKBranching
open scoped BigOperators Nat
open Finset Equiv

/-- Pairings of distinguished objects, encoded as actual partner permutations. -/
def Pairing (H : Type*) [Fintype H] [DecidableEq H] :=
  {σ : Equiv.Perm H // σ ^ 2 = 1 ∧ ∀ h, σ h ≠ h}

instance {H : Type*} [Fintype H] [DecidableEq H] : Fintype (Pairing H) := by
  classical
  unfold Pairing
  infer_instance

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Every pairing on 2k objects has exactly k two-cycles. -/
theorem pairing_cycleType {k : ℕ} (hH : Fintype.card H = 2 * k) (σ : Pairing H) :
    σ.val.cycleType = Multiset.replicate k 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one σ.property.1
  have hs : σ.val.support = Finset.univ := by
    ext h
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact σ.property.2 h
  have hsum := congrArg Multiset.sum hrep
  rw [σ.val.sum_cycleType, hs, Finset.card_univ, hH, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at hsum
  have hk : σ.val.cycleType.card = k := by omega
  simpa only [hk] using hrep

/-- Factorial identity including the empty pairing convention (-1)!! = 1. -/
theorem factorial_two_mul (k : ℕ) :
    (2 * k).factorial = (2 * k - 1)‼ * (2 ^ k * k.factorial) := by
  cases k with
  | zero => simp
  | succ k =>
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, Nat.doubleFactorial_two_mul] at h
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    simpa only [mul_comm] using h

/-- The exact permutation cycle-type count bounds actual half-edge pairings. -/
theorem card_pairings_le {k : ℕ} (hH : Fintype.card H = 2 * k) :
    Fintype.card (Pairing H) ≤ (2 * k - 1)‼ := by
  classical
  let C : Finset (Equiv.Perm H) := Finset.univ.filter
    (fun σ => σ.cycleType = Multiset.replicate k 2)
  have hcard : Fintype.card (Pairing H) ≤ C.card := by
    rw [← Fintype.card_coe C]
    apply Fintype.card_le_of_injective
      (fun σ : Pairing H => (⟨σ.val, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, pairing_cycleType hH σ⟩⟩ : C))
    intro σ τ h
    exact Subtype.ext (congrArg (fun t : C => t.val) h)
  have hcycle := Equiv.Perm.card_of_cycleType_mul_eq H (Multiset.replicate k 2)
  have hcount : (∏ n ∈ (Multiset.replicate k 2).toFinset,
      ((Multiset.replicate k 2).count n).factorial) = k.factorial := by
    by_cases hk : k = 0
    · subst k; simp
    · simp [Multiset.toFinset_replicate, hk]
  have hvalid : (Multiset.replicate k 2).sum ≤ Fintype.card H ∧
      ∀ a ∈ Multiset.replicate k 2, 2 ≤ a := by
    constructor
    · simp [hH, Nat.mul_comm]
    · intro a ha
      exact (Multiset.mem_replicate.mp ha).2 ▸ le_rfl
  rw [if_pos hvalid, hcount] at hcycle
  have hmul : C.card * (2 ^ k * k.factorial) = (2 * k).factorial := by
    simpa [C, hH, Nat.mul_comm] using hcycle
  have hle := Nat.mul_le_mul_right (2 ^ k * k.factorial) hcard
  rw [hmul, factorial_two_mul] at hle
  exact Nat.le_of_mul_le_mul_right hle (by positivity)

/-- Product form of the odd double factorial, including zero pairs. -/
theorem odd_doubleFactorial_eq_prod (k : ℕ) :
    (2 * k - 1)‼ = ∏ j ∈ Finset.range k, (2 * j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k = 0
    · subst k; simp
    · rw [Finset.prod_range_succ, ← ih]
      have hstep : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
      rw [hstep, Nat.doubleFactorial_add_two]
      rw [show 2 * k - 1 + 2 = 2 * k + 1 by omega]
      exact mul_comm _ _

/-- The growing-order double-factorial estimate used in the SK mass bound. -/
theorem odd_doubleFactorial_le_pow (k : ℕ) : (2 * k - 1)‼ ≤ (2 * k) ^ k := by
  rw [odd_doubleFactorial_eq_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range k, 2 * k := by
      apply Finset.prod_le_prod'
      intro j hj
      have hj' := Finset.mem_range.mp hj
      omega
    _ = _ := by simp

end SpinGlass.SKBranching
