import Std

/-!
# Degree reduction for the SK algebra

The relation is `y^6 = y^4`: degrees at least four retain parity.
In particular this is not truncation at degree four. These declarations
verify the degree arithmetic only; they do not certify the full paper.
-/

namespace SpinGlass

/-- Canonical exponent for the relation `y^6 = y^4`. -/
def rho (n : Nat) : Nat := if n < 4 then n else 4 + n % 2

/-- The definition agrees with the paper's three-way description. -/
theorem rho_formula (n : Nat) :
    rho n = if n ≤ 3 then n else if n % 2 = 0 then 4 else 5 := by
  unfold rho
  split <;> split <;> try omega
  all_goals split <;> omega

/-- Reduction always lands in the six canonical degrees. -/
theorem rho_lt_six (n : Nat) : rho n < 6 := by
  unfold rho
  split <;> omega

/-- The canonical representatives are fixed by reduction. -/
theorem rho_of_lt_six (n : Nat) (hn : n < 6) : rho n = n := by
  unfold rho
  split <;> omega

@[simp] theorem rho_zero : rho 0 = 0 := by decide
@[simp] theorem rho_one : rho 1 = 1 := by decide
@[simp] theorem rho_two : rho 2 = 2 := by decide
@[simp] theorem rho_three : rho 3 = 3 := by decide
@[simp] theorem rho_four : rho 4 = 4 := by decide
@[simp] theorem rho_five : rho 5 = 5 := by decide
@[simp] theorem rho_six : rho 6 = 4 := by decide

/-- Reduction preserves parity, including below the threshold. -/
theorem rho_mod_two (n : Nat) : rho n % 2 = n % 2 := by
  unfold rho
  split <;> omega

/-- Exactly degrees at least four reduce to a degree at least four. -/
theorem four_le_rho_iff (n : Nat) : 4 ≤ rho n ↔ 4 ≤ n := by
  unfold rho
  split <;> omega

/-- The retained fourth-degree class is precisely the even high degrees. -/
theorem rho_eq_four_iff (n : Nat) : rho n = 4 ↔ 4 ≤ n ∧ n % 2 = 0 := by
  unfold rho
  split <;> omega

/-- The fifth-degree class is precisely the odd high degrees. -/
theorem rho_eq_five_iff (n : Nat) : rho n = 5 ↔ 4 ≤ n ∧ n % 2 = 1 := by
  unfold rho
  split <;> omega

/-- Below degree four, reduction cannot conceal a different exponent. -/
theorem rho_eq_small_iff (n i : Nat) (hi : i < 4) : rho n = i ↔ n = i := by
  unfold rho
  split <;> omega

/-- Reduced equality retains exact low degrees and parity of high degrees. -/
theorem rho_eq_iff (d e : Nat) :
    rho d = rho e ↔ (d < 4 ∧ d = e) ∨ (4 ≤ d ∧ 4 ≤ e ∧ d % 2 = e % 2) := by
  unfold rho
  split <;> split <;> omega

/-- The generating algebra relation persists after multiplication by any power. -/
theorem rho_add_six_eq_add_four (n : Nat) : rho (n + 6) = rho (n + 4) := by
  unfold rho
  split <;> split <;> omega

/-- Reduction can be performed before adding another degree. -/
theorem rho_add_left (d e : Nat) : rho (rho d + e) = rho (d + e) := by
  unfold rho
  split <;> (try split) <;> (try split) <;> omega

/-- Reduction can equally be performed on the second summand. -/
theorem rho_add_right (d e : Nat) : rho (d + rho e) = rho (d + e) := by
  simpa [Nat.add_comm] using rho_add_left e d

/-- Both summands can be reduced before addition. -/
theorem rho_add_both (d e : Nat) : rho (rho d + rho e) = rho (d + e) := by
  rw [rho_add_left, rho_add_right]

@[simp] theorem rho_idempotent (n : Nat) : rho (rho n) = rho n :=
  rho_of_lt_six (rho n) (rho_lt_six n)

/-- The six representatives of exponent classes. -/
structure CappedDegree where
  toFin : Fin 6
  deriving DecidableEq

namespace CappedDegree

/-- The representative exponent carried by a degree state. -/
def val (a : CappedDegree) : Nat := a.toFin.val

theorem isLt (a : CappedDegree) : a.val < 6 := a.toFin.isLt

/-- Degree states agree exactly when their representative exponents agree. -/
theorem ext_val {a b : CappedDegree} (h : a.val = b.val) : a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      have hab : a = b := Fin.ext h
      cases hab
      rfl

/-- Reduce an arbitrary exponent to its canonical representative. -/
def ofNat (n : Nat) : CappedDegree := ⟨⟨rho n, rho_lt_six n⟩⟩

/-- Addition is exponent addition followed by reduction. -/
def add (a b : CappedDegree) : CappedDegree := ofNat (a.val + b.val)

instance : Zero CappedDegree := ⟨⟨⟨0, by decide⟩⟩⟩
instance : Add CappedDegree := ⟨add⟩

@[simp] theorem val_ofNat (n : Nat) : (ofNat n).val = rho n := rfl
@[simp] theorem val_zero : (0 : CappedDegree).val = 0 := rfl
@[simp] theorem val_add (a b : CappedDegree) : (a + b).val = rho (a.val + b.val) := rfl

@[simp] theorem ofNat_val (a : CappedDegree) : ofNat a.val = a := by
  apply ext_val
  exact rho_of_lt_six a.val a.isLt

/-- The quotient map preserves addition. -/
theorem ofNat_add (d e : Nat) : ofNat (d + e) = ofNat d + ofNat e := by
  apply ext_val
  exact (rho_add_both d e).symm

theorem add_assoc (a b c : CappedDegree) : (a + b) + c = a + (b + c) := by
  apply ext_val
  change rho (rho (a.val + b.val) + c.val) = rho (a.val + rho (b.val + c.val))
  rw [rho_add_left, rho_add_right, Nat.add_assoc]

theorem add_comm (a b : CappedDegree) : a + b = b + a := by
  apply ext_val
  change rho (a.val + b.val) = rho (b.val + a.val)
  rw [Nat.add_comm]

@[simp] theorem zero_add (a : CappedDegree) : 0 + a = a := by
  apply ext_val
  change rho (0 + a.val) = a.val
  simpa using rho_of_lt_six a.val a.isLt

@[simp] theorem add_zero (a : CappedDegree) : a + 0 = a := by
  rw [add_comm, zero_add]

end CappedDegree

end SpinGlass
