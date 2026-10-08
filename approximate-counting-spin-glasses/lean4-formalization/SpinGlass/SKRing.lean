import SpinGlass.SKCoefficient
import SpinGlass.SKExponential
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Module.Rat

/-!
# The concrete SK coefficient arrays form a rational algebra

A distinct wrapper prevents accidental use of pointwise multiplication of
functions. Its ring multiplication is exactly the verified dense coefficient
update. Rational scalar multiplication is real coefficient-field scaling.
-/

noncomputable section

namespace SpinGlass.SKRing

open scoped BigOperators

/-- A coefficient array equipped with the actual SK algebra multiplication. -/
structure Element (b L : ℕ) where
  coeff : SKCoefficient.Coefficients b L

@[ext] theorem ext {b L : ℕ} {f g : Element b L} (h : f.coeff = g.coeff) : f = g := by
  cases f
  cases g
  congr

instance {b L : ℕ} : Zero (Element b L) := ⟨⟨0⟩⟩
instance {b L : ℕ} : One (Element b L) := ⟨⟨SKCoefficient.one b L⟩⟩
instance {b L : ℕ} : Add (Element b L) := ⟨fun f g => ⟨f.coeff + g.coeff⟩⟩
instance {b L : ℕ} : Neg (Element b L) := ⟨fun f => ⟨-f.coeff⟩⟩
instance {b L : ℕ} : Mul (Element b L) := ⟨fun f g => ⟨SKCoefficient.mul f.coeff g.coeff⟩⟩

@[simp] theorem coeff_zero {b L : ℕ} : (0 : Element b L).coeff = 0 := rfl
@[simp] theorem coeff_one {b L : ℕ} : (1 : Element b L).coeff = SKCoefficient.one b L := rfl
@[simp] theorem coeff_add {b L : ℕ} (f g : Element b L) :
    (f + g).coeff = f.coeff + g.coeff := rfl
@[simp] theorem coeff_neg {b L : ℕ} (f : Element b L) : (-f).coeff = -f.coeff := rfl
@[simp] theorem coeff_mul {b L : ℕ} (f g : Element b L) :
    (f * g).coeff = SKCoefficient.mul f.coeff g.coeff := rfl

instance {b L : ℕ} : CommRing (Element b L) :=
  CommRing.ofMinimalAxioms
    (fun f g h => by apply ext; exact add_assoc _ _ _)
    (fun f => by apply ext; exact zero_add _)
    (fun f => by apply ext; exact neg_add_cancel _)
    (fun f g h => by apply ext; exact SKCoefficient.mul_assoc _ _ _)
    (fun f g => by apply ext; exact SKCoefficient.mul_comm _ _)
    (fun f => by apply ext; exact SKCoefficient.one_mul _)
    (fun f g h => by apply ext; exact SKCoefficient.mul_add _ _ _)

instance {b L : ℕ} : SMul ℚ (Element b L) :=
  ⟨fun q f => ⟨SKCoefficient.scale (q : ℝ) f.coeff⟩⟩

@[simp] theorem coeff_rat_smul {b L : ℕ} (q : ℚ) (f : Element b L) :
    (q • f).coeff = SKCoefficient.scale (q : ℝ) f.coeff := rfl

instance {b L : ℕ} : Module ℚ (Element b L) where
  one_smul f := by apply ext; simp
  mul_smul q r f := by apply ext; simp [SKCoefficient.scale_scale]
  smul_add q f g := by apply ext; funext z; simp [SKCoefficient.scale, mul_add]
  smul_zero q := by apply ext; funext z; simp [SKCoefficient.scale]
  add_smul q r f := by apply ext; funext z; simp [SKCoefficient.scale, add_mul]
  zero_smul f := by apply ext; funext z; simp [SKCoefficient.scale]

/-- Wrapper powers are exactly the dense powers used in the implementation. -/
@[simp] theorem coeff_pow {b L : ℕ} (f : Element b L) (n : ℕ) :
    (f ^ n).coeff = SKCoefficient.pow f.coeff n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, coeff_mul, ih]; rfl

/-- Wrapper sums preserve every coefficient coordinate. -/
@[simp] theorem coeff_sum {b L : ℕ} {I : Type*} (s : Finset I) (f : I → Element b L) :
    (∑ i ∈ s, f i).coeff = ∑ i ∈ s, (f i).coeff := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Ordinary basis monomials embed with their exact signed coefficients. -/
def monomial {b L : ℕ} (x : SKCoefficient.Basis b L) (a : ℝ) : Element b L :=
  ⟨SKCoefficient.single x a⟩

/-- Every primitive monomial consuming an outside color has square zero. -/
theorem monomial_sq_zero {b L : ℕ} (x : SKCoefficient.Basis b L) (a : ℝ)
    (hx : x.2.1.Nonempty) : monomial x a ^ 2 = 0 := by
  apply ext
  rw [pow_two, coeff_mul]
  apply SKCoefficient.mul_single_single_rejected
  intro hc
  exact Finset.not_disjoint_iff.mpr ⟨hx.choose, hx.choose_spec, hx.choose_spec⟩ hc.2

/-- The complete color ideal is nilpotent in the concrete ring as well. -/
theorem color_ideal_pow_zero {b L : ℕ} (f : Element b L)
    (hf : SKCoefficient.VanishesBelow 1 f.coeff) : f ^ (L + 1) = 0 := by
  apply ext
  rw [coeff_pow]
  exact SKCoefficient.pow_colors_succ_eq_zero f.coeff hf

/-- Rational factorial coefficients become exactly the real divisions in Algorithm 5. -/
theorem factorial_term_coeff {b L : ℕ} (f : Element b L) (n : ℕ) :
    ((n.factorial : ℚ)⁻¹ • (f ^ n)).coeff = SKExponential.term f.coeff n := by
  simp [SKExponential.term]

end SpinGlass.SKRing
