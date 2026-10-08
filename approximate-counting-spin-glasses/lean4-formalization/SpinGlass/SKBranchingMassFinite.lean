import SpinGlass.SKBranchingRealizations
import SpinGlass.SKBranchingGaussian
import SpinGlass.SKBranchingSeries
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite degree-sequence majorization of actual SK graph mass

All sums in this step are finite. Actual graph realizations are grouped by their
degrees and bounded using the proved distinguished-stub injection. The resulting
sum is exactly an auxiliary Gaussian expectation of the finite product of
vertex degree polynomials.
-/
noncomputable section
namespace SpinGlass.SKBranching
open scoped BigOperators Nat
open MeasureTheory Finset Real
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Gaussian integrability predicate includes its actual density factor. -/
def GaussianIntegrable (f : ℝ → ℝ) : Prop :=
  Integrable (fun x : ℝ => f x * Real.exp (-(1 / 2 : ℝ) * x ^ 2))

/-- Finite linearity of the normalized Gaussian functional. -/
theorem gaussianMean_sum {I : Type*} (A : Finset I) (f : I → ℝ → ℝ)
    (hf : ∀ i ∈ A, GaussianIntegrable (f i)) :
    gaussianMean (fun x => ∑ i ∈ A, f i x) = ∑ i ∈ A, gaussianMean (f i) := by
  unfold gaussianMean
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum A hf, Finset.mul_sum]

/-- Multiplying by a real constant commutes with the Gaussian functional. -/
theorem gaussianMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    gaussianMean (fun x => c * f x) = c * gaussianMean f := by
  unfold gaussianMean
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

/-- Monotonicity with explicit nonnegativity and integrability. -/
theorem gaussianMean_mono (f g : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : GaussianIntegrable g) (hfg : ∀ x, f x ≤ g x) : gaussianMean f ≤ gaussianMean g := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_of_nonneg
    (ae_of_all _ fun x => mul_nonneg (hf x) (Real.exp_pos _).le) hg
  exact ae_of_all _ fun x => mul_le_mul_of_nonneg_right (hfg x) (Real.exp_pos _).le

/-- The finite degree generating monomial with the exact factorial denominator. -/
def degreeMonomial (r : ℝ) (d : V → ℕ) (x : ℝ) : ℝ :=
  ∏ v, (Real.sqrt r * x) ^ d v / (d v).factorial

theorem degreeMonomial_eq (r : ℝ) (hr : 0 ≤ r) (d : V → ℕ)
    {k : ℕ} (hsum : ∑ v, d v = 2 * k) (x : ℝ) :
    degreeMonomial r d x = (r ^ k / ∏ v, ((d v).factorial : ℝ)) * x ^ (2 * k) := by
  unfold degreeMonomial
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum, mul_pow]
  have hsqrt : Real.sqrt r ^ (2 * k) = r ^ k := by rw [pow_mul, Real.sq_sqrt hr]
  rw [hsqrt]
  ring

theorem gaussianIntegrable_degreeMonomial (r : ℝ) (hr : 0 ≤ r) (d : V → ℕ)
    {k : ℕ} (hsum : ∑ v, d v = 2 * k) : GaussianIntegrable (degreeMonomial r d) := by
  unfold GaussianIntegrable
  simp_rw [degreeMonomial_eq r hr d hsum, mul_assoc]
  exact (integrable_even_gaussian k (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _

/-- Actual auxiliary Gaussian moment of each degree-sequence monomial. -/
theorem gaussianMean_degreeMonomial (r : ℝ) (hr : 0 ≤ r) (d : V → ℕ)
    {k : ℕ} (hsum : ∑ v, d v = 2 * k) :
    gaussianMean (degreeMonomial r d) =
      ((2 * k - 1)‼ : ℝ) / (∏ v, ((d v).factorial : ℝ)) * r ^ k := by
  have hg : gaussianMean (fun x : ℝ => x ^ (2 * k)) = ((2 * k - 1)‼ : ℝ) := by
    simpa only [zero_mul, zero_div, Real.exp_zero, mul_one, sub_zero, Real.one_rpow] using
      gaussianMean_tilted_even_moment k (t := 0) (by norm_num)
  have heq : degreeMonomial r d =
      (fun x : ℝ => (r ^ k / ∏ v, ((d v).factorial : ℝ)) * x ^ (2 * k)) :=
    funext (degreeMonomial_eq r hr d hsum)
  rw [heq, gaussianMean_const_mul, hg]
  ring

/-- All-vertex handshaking for actual two-element-edge simple graphs. -/
theorem sum_degrees_simple (Γ : Finset (Finset V)) (hsimple : ∀ e ∈ Γ, e.card = 2) :
    (∑ v, SpinGlass.Hypergraph.degree Γ v) = 2 * Γ.card := by
  calc
    _ = ∑ e ∈ Γ, (Finset.univ.filter (fun v => v ∈ e)).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun (v : V) (e : Finset V) => v ∈ e)
    _ = ∑ e ∈ Γ, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      simpa using hsimple e he
    _ = _ := by simp [Nat.mul_comm]

/-- The exact degree fiber of any selected finite family is a subtype of
all actual realizations of those degrees. -/
theorem degree_fiber_card_le (F : Finset (Finset (Finset V)))
    (hF : ∀ Γ ∈ F, ∀ e ∈ Γ, e.card = 2) (d : V → ℕ) :
    (F.filter (fun Γ => SpinGlass.Hypergraph.degree Γ = d)).card ≤
      Fintype.card (Realization d) := by
  classical
  rw [← Fintype.card_coe]
  apply Fintype.card_le_of_injective
    (fun Γ : F.filter (fun Γ => SpinGlass.Hypergraph.degree Γ = d) =>
      (⟨Γ.val, hF Γ.val (Finset.mem_filter.mp Γ.property).1,
        fun v => congrFun (Finset.mem_filter.mp Γ.property).2 v⟩ : Realization d))
  intro Γ Δ h
  exact Subtype.ext (congrArg (fun Γ : Realization d => Γ.val) h)

/-- The weighted mass of an actual degree fiber is bounded by its Gaussian
monomial, using the proved realization multiplicity. -/
theorem degree_fiber_mass_le (F : Finset (Finset (Finset V)))
    (hF : ∀ Γ ∈ F, ∀ e ∈ Γ, e.card = 2) (r : ℝ) (hr : 0 ≤ r) (d : V → ℕ)
    {k : ℕ} (hsum : ∑ v, d v = 2 * k) :
    (∑ Γ ∈ F.filter (fun Γ => SpinGlass.Hypergraph.degree Γ = d), r ^ Γ.card) ≤
      gaussianMean (degreeMonomial r d) := by
  have hc (Γ : Finset (Finset V))
      (hΓ : Γ ∈ F.filter (fun Γ => SpinGlass.Hypergraph.degree Γ = d)) : Γ.card = k := by
    have hh := sum_degrees_simple Γ (hF Γ (Finset.mem_filter.mp hΓ).1)
    rw [(Finset.mem_filter.mp hΓ).2, hsum] at hh
    omega
  rw [Finset.sum_congr rfl (fun Γ hΓ => congrArg (fun n : ℕ => r ^ n) (hc Γ hΓ)),
    Finset.sum_const, nsmul_eq_mul, gaussianMean_degreeMonomial r hr d hsum]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr k)
  have hcount := (Nat.mul_le_mul_right (∏ v, (d v).factorial) (degree_fiber_card_le F hF d)).trans
    (degree_realization_count_mul_factorials d hsum)
  apply (le_div_iff₀ (Finset.prod_pos (fun v _ => by exact_mod_cast Nat.factorial_pos (d v)))).mpr
  exact_mod_cast hcount

/-- Grouping actual graph mass into finite degree fibers gives its explicit
finite auxiliary-Gaussian bound. -/
theorem finite_degree_mass_le_gaussian (F : Finset (Finset (Finset V)))
    (hF : ∀ Γ ∈ F, ∀ e ∈ Γ, e.card = 2) (r : ℝ) (hr : 0 ≤ r)
    (D : Finset (V → ℕ))
    (hcover : ∀ Γ ∈ F, SpinGlass.Hypergraph.degree Γ ∈ D)
    (heven : ∀ d ∈ D, ∃ k, ∑ v, d v = 2 * k) :
    (∑ Γ ∈ F, r ^ Γ.card) ≤ gaussianMean (fun x => ∑ d ∈ D, degreeMonomial r d x) := by
  rw [gaussianMean_sum D _ (fun d hd => by
    obtain ⟨k, hk⟩ := heven d hd
    exact gaussianIntegrable_degreeMonomial r hr d hk),
    ← Finset.sum_fiberwise_of_maps_to hcover]
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨k, hk⟩ := heven d hd
  exact degree_fiber_mass_le F hF r hr d hk

end SpinGlass.SKBranching
