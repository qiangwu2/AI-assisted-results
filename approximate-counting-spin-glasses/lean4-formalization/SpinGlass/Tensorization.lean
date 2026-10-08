import SpinGlass.Noise
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Conditional tensorization of reverse power-mean bounds

The hypotheses in this file include a lower bound for a one-coordinate kernel.
The conclusion propagates that bound to the explicit product kernel. This is a
conditional tensorization theorem, not a proof of the scalar inequality.
-/

noncomputable section
open Finset
namespace SpinGlass.Tensorization

/-- A weighted power mean; the weights need not be normalized for the
product tensorization identity. -/
def powerMean {A : Type*} [Fintype A] (μ : A → ℝ) (r : ℝ) (f : A → ℝ) : ℝ :=
  (∑ a, μ a * (f a) ^ r) ^ (1 / r)

/-- The bilinear form of a finite joint kernel. -/
def bilinear {A B : Type*} [Fintype A] [Fintype B]
    (K : A → B → ℝ) (f : A → ℝ) (g : B → ℝ) : ℝ :=
  ∑ a, ∑ b, K a b * f a * g b

/-- A conditional reverse power-mean estimate for all strictly positive inputs. -/
def HasReverseBound {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (K : A → B → ℝ) (r t : ℝ) : Prop :=
  ∀ f g, (∀ a, 0 < f a) → (∀ b, 0 < g b) →
    powerMean μ r f * powerMean ν t g ≤ bilinear K f g

lemma powerMean_pos {A : Type*} [Fintype A] [Nonempty A]
    {μ f : A → ℝ} {r : ℝ} (hμ : ∀ a, 0 < μ a) (hf : ∀ a, 0 < f a) :
    0 < powerMean μ r f := by
  apply Real.rpow_pos_of_pos
  exact Finset.sum_pos (fun a _ => mul_pos (hμ a) (Real.rpow_pos_of_pos (hf a) r))
    Finset.univ_nonempty

lemma powerMean_rpow {A : Type*} [Fintype A]
    {μ f : A → ℝ} {r : ℝ} (hμ : ∀ a, 0 ≤ μ a) (hf : ∀ a, 0 ≤ f a)
    (hr : r ≠ 0) :
    (powerMean μ r f) ^ r = ∑ a, μ a * (f a) ^ r := by
  unfold powerMean
  rw [one_div, Real.rpow_inv_rpow]
  · exact Finset.sum_nonneg (fun a _ => mul_nonneg (hμ a) (Real.rpow_nonneg (hf a) r))
  · exact hr

/-- Taking the same weighted power mean in two coordinates flattens exactly. -/
lemma powerMean_product {A C : Type*} [Fintype A] [Fintype C]
    (μ : A → ℝ) (ξ : C → ℝ) (r : ℝ) (f : A × C → ℝ)
    (hξ : ∀ c, 0 ≤ ξ c) (hf : ∀ a, 0 ≤ f a) (hr : r ≠ 0) :
    powerMean μ r (fun a => powerMean ξ r (fun c => f (a,c))) =
      powerMean (fun a : A × C => μ a.1 * ξ a.2) r f := by
  unfold powerMean
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  have h : ((∑ c, ξ c * f (a,c) ^ r) ^ (1 / r)) ^ r =
      ∑ c, ξ c * f (a,c) ^ r :=
    powerMean_rpow hξ (fun c => hf (a,c)) hr
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

lemma bilinear_product {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (K : A → B → ℝ) (L : C → D → ℝ) (f : A × C → ℝ) (g : B × D → ℝ) :
    bilinear (fun a b => K a.1 b.1 * L a.2 b.2) f g =
      ∑ a, ∑ b, K a b * bilinear L (fun c => f (a,c)) (fun d => g (b,d)) := by
  simp only [bilinear, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Reverse bilinear bounds are closed under independent products of kernels.
The nonnegativity of the outer kernel makes the conditional inner bound valid
inside the outer sum. -/
theorem HasReverseBound.product {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty C] [Nonempty D]
    {μ : A → ℝ} {ν : B → ℝ} {ξ : C → ℝ} {η : D → ℝ}
    {K : A → B → ℝ} {L : C → D → ℝ} {r t : ℝ}
    (hK : HasReverseBound μ ν K r t) (hL : HasReverseBound ξ η L r t)
    (hK0 : ∀ a b, 0 ≤ K a b) (hξ : ∀ c, 0 < ξ c) (hη : ∀ d, 0 < η d)
    (hr : r ≠ 0) (ht : t ≠ 0) :
    HasReverseBound (fun a : A × C => μ a.1 * ξ a.2)
      (fun b : B × D => ν b.1 * η b.2)
      (fun a b => K a.1 b.1 * L a.2 b.2) r t := by
  intro f g hf hg
  rw [← powerMean_product μ ξ r f (fun c => (hξ c).le) (fun a => (hf a).le) hr]
  rw [← powerMean_product ν η t g (fun d => (hη d).le) (fun b => (hg b).le) ht]
  apply le_trans (hK _ _
    (fun a => powerMean_pos hξ (fun c => hf (a,c)))
    (fun b => powerMean_pos hη (fun d => hg (b,d))))
  rw [bilinear_product]
  unfold bilinear
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hL _ _ (fun c => hf (a,c)) (fun d => hg (b,d)))
    (hK0 a b)

/-- Transfer a conditional estimate across finite equivalences. -/
lemma HasReverseBound.of_equiv {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {μ : A → ℝ} {ν : B → ℝ} {ξ : C → ℝ} {η : D → ℝ}
    {K : A → B → ℝ} {L : C → D → ℝ} {r t : ℝ}
    (h : HasReverseBound μ ν K r t) (e : A ≃ C) (e' : B ≃ D)
    (hμ : ∀ a, μ a = ξ (e a)) (hν : ∀ b, ν b = η (e' b))
    (hK : ∀ a b, K a b = L (e a) (e' b)) :
    HasReverseBound ξ η L r t := by
  intro f g hf hg
  have h' := h (fun a => f (e a)) (fun b => g (e' b))
    (fun a => hf (e a)) (fun b => hg (e' b))
  have hm : powerMean μ r (fun a => f (e a)) = powerMean ξ r f := by
    unfold powerMean
    congr 1
    exact Fintype.sum_equiv e _ _ (fun a => by rw [hμ a])
  have hn : powerMean ν t (fun b => g (e' b)) = powerMean η t g := by
    unfold powerMean
    congr 1
    exact Fintype.sum_equiv e' _ _ (fun b => by rw [hν b])
  have hb : bilinear K (fun a => f (e a)) (fun b => g (e' b)) = bilinear L f g := by
    unfold bilinear
    apply Fintype.sum_equiv e
    intro a
    exact Fintype.sum_equiv e' _ _ (fun b => by rw [hK a b])
  rwa [hm, hn, hb] at h'

/-- The explicit independent product of coordinate weights. -/
def productWeight {C : Type*} {n : ℕ} (μ : C → ℝ) (x : Fin n → C) : ℝ :=
  ∏ i, μ (x i)

/-- The explicit independent product of coordinate joint kernels. -/
def productKernel {C D : Type*} {n : ℕ}
    (K : C → D → ℝ) (x : Fin n → C) (y : Fin n → D) : ℝ :=
  ∏ i, K (x i) (y i)

/-- A scalar reverse bilinear inequality tensorizes to every finite product of
that same kernel. No restriction on the nonzero exponents is needed by the
induction itself. -/
theorem HasReverseBound.finite_product {C D : Type*}
    [Fintype C] [Fintype D] [Nonempty C] [Nonempty D]
    {μ : C → ℝ} {ν : D → ℝ} {K : C → D → ℝ} {r t : ℝ}
    (h : HasReverseBound μ ν K r t)
    (hμ : ∀ c, 0 < μ c) (hν : ∀ d, 0 < ν d) (hK : ∀ c d, 0 ≤ K c d)
    (hr : r ≠ 0) (ht : t ≠ 0) (n : ℕ) :
    HasReverseBound (productWeight (n := n) μ) (productWeight (n := n) ν)
      (productKernel K) r t := by
  induction n with
  | zero =>
    intro f g hf hg
    simp only [powerMean, bilinear, productWeight, productKernel, Fin.prod_univ_zero,
      one_mul, Fintype.sum_unique]
    rw [one_div, Real.rpow_rpow_inv (hf _).le hr,
      one_div, Real.rpow_rpow_inv (hg _).le ht]
  | succ n ih =>
    have hp := h.product ih hK
      (fun x => Finset.prod_pos (fun i _ => hμ (x i)))
      (fun y => Finset.prod_pos (fun i _ => hν (y i))) hr ht
    apply hp.of_equiv (Fin.consEquiv (fun _ : Fin (n+1) => C))
      (Fin.consEquiv (fun _ : Fin (n+1) => D))
    · intro x
      change μ x.1 * (∏ i, μ (x.2 i)) = ∏ i, μ ((Fin.cons x.1 x.2 : Fin (n+1) → C) i)
      rw [Fin.prod_univ_succ]
      simp
    · intro y
      change ν y.1 * (∏ i, ν (y.2 i)) = ∏ i, ν ((Fin.cons y.1 y.2 : Fin (n+1) → D) i)
      rw [Fin.prod_univ_succ]
      simp
    · intro x y
      change K x.1 y.1 * (∏ i, K (x.2 i) (y.2 i)) =
        ∏ i, K ((Fin.cons x.1 x.2 : Fin (n+1) → C) i) ((Fin.cons y.1 y.2 : Fin (n+1) → D) i)
      rw [Fin.prod_univ_succ]
      simp

/-- Reindexing gives the same explicit product bound for any finite coordinate
type, including the empty coordinate type. -/
theorem HasReverseBound.fintype_product {ι C D : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype D] [Nonempty C] [Nonempty D]
    {μ : C → ℝ} {ν : D → ℝ} {K : C → D → ℝ} {r t : ℝ}
    (h : HasReverseBound μ ν K r t)
    (hμ : ∀ c, 0 < μ c) (hν : ∀ d, 0 < ν d) (hK : ∀ c d, 0 ≤ K c d)
    (hr : r ≠ 0) (ht : t ≠ 0) :
    HasReverseBound (fun x : ι → C => ∏ i, μ (x i))
      (fun y : ι → D => ∏ i, ν (y i)) (fun x y => ∏ i, K (x i) (y i)) r t := by
  let e := Fintype.equivFin ι
  have hn := h.finite_product hμ hν hK hr ht (Fintype.card ι)
  apply hn.of_equiv (Equiv.arrowCongr e.symm (Equiv.refl C))
    (Equiv.arrowCongr e.symm (Equiv.refl D))
  · intro x
    exact (e.prod_comp (fun j => μ (x j))).symm
  · intro y
    exact (e.prod_comp (fun j => ν (y j))).symm
  · intro x y
    exact (e.prod_comp (fun j => K (x j) (y j))).symm

/-- The uniform correlated joint distribution on a single pair of bits. -/
def bitJoint (θ : ℝ) (a b : Bool) : ℝ :=
  (1 / 2) * Noise.noiseWeight θ (Bool.xor a b)

lemma powerMean_bool (r : ℝ) (f : Bool → ℝ) :
    powerMean (fun _ : Bool => 1 / 2) r f =
      ((f false ^ r + f true ^ r) / 2) ^ (1 / r) := by
  unfold powerMean
  congr 1
  simp only [Fintype.sum_bool]
  ring

lemma bilinear_bitJoint (θ : ℝ) (f g : Bool → ℝ) :
    bilinear (bitJoint θ) f g =
      ((f false + f true) / 2) * ((g false + g true) / 2) +
      θ * ((f false - f true) / 2) * ((g false - g true) / 2) := by
  simp [bilinear, bitJoint, Noise.noiseWeight]
  ring

/-- Conditional Boolean-cube tensorization, stated for the actual product
joint kernel. The analytic one-bit bound is an explicit hypothesis. -/
theorem bool_cube_reverse_bound {θ r t : ℝ}
    (hθ : -1 ≤ θ) (hθ1 : θ ≤ 1) (hr : r ≠ 0) (ht : t ≠ 0)
    (hbit : HasReverseBound (fun _ : Bool => 1 / 2) (fun _ : Bool => 1 / 2)
      (bitJoint θ) r t) (n : ℕ) :
    HasReverseBound (productWeight (n := n) (fun _ : Bool => 1 / 2))
      (productWeight (n := n) (fun _ : Bool => 1 / 2))
      (productKernel (bitJoint θ)) r t := by
  exact hbit.finite_product (fun _ => by norm_num) (fun _ => by norm_num)
    (fun a b => mul_nonneg (by norm_num) (Noise.noiseWeight_nonneg hθ hθ1 _)) hr ht n

/-- The conditional Boolean result for a general finite coordinate set. -/
theorem bool_cube_reverse_bound_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {θ r t : ℝ}
    (hθ : -1 ≤ θ) (hθ1 : θ ≤ 1) (hr : r ≠ 0) (ht : t ≠ 0)
    (hbit : HasReverseBound (fun _ : Bool => 1 / 2) (fun _ : Bool => 1 / 2)
      (bitJoint θ) r t) :
    HasReverseBound (fun _ : ι → Bool => (1 / 2 : ℝ) ^ Fintype.card ι)
      (fun _ : ι → Bool => (1 / 2 : ℝ) ^ Fintype.card ι)
      (fun x y => ∏ i, bitJoint θ (x i) (y i)) r t := by
  simpa only [Finset.prod_const, Finset.card_univ] using
    hbit.fintype_product (ι := ι) (fun _ => by norm_num) (fun _ => by norm_num)
      (fun a b => mul_nonneg (by norm_num) (Noise.noiseWeight_nonneg hθ hθ1 _)) hr ht

end SpinGlass.Tensorization
