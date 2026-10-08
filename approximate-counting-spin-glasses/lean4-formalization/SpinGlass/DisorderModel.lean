import SpinGlass.Partition
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration

/-!
# Arbitrary symmetric real disorder

The disorder measure is an actual probability measure on the reals. Symmetry means
invariance under negation, and the finite array has its product law. No density,
non-atomicity, bounded support, or higher moment assumption is imposed.
-/

noncomputable section
namespace SpinGlass.Disorder

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- The manuscript's symmetry hypothesis, expressed at the level of the law. -/
def SymmetricLaw (μ : Measure ℝ) : Prop := μ.map (fun x : ℝ => -x) = μ

/-- The second-moment assumption is stated with integrability, so the Bochner
integral cannot silently evaluate to zero on a nonintegrable function. -/
structure UnitSecondMoment (μ : Measure ℝ) : Prop where
  integrable_sq : Integrable (fun x : ℝ => x ^ 2) μ
  integral_sq : (∫ x : ℝ, x ^ 2 ∂μ) = 1

/-- The actual finite iid disorder law. -/
def iidLaw {E : Type*} [Fintype E] (μ : Measure ℝ) : Measure (E → ℝ) :=
  Measure.pi (fun _ : E => μ)

instance iidLaw_probability {E : Type*} [Fintype E] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (iidLaw (E := E) μ) := by
  unfold iidLaw
  infer_instance

/-- Edge weight including any real inverse-temperature/scaling coefficient. -/
def weight (a x : ℝ) : ℝ := Real.tanh (a * x)

/-- Single-edge second moment; this is not supplied as an independent assumption. -/
def secondMoment (μ : Measure ℝ) (a : ℝ) : ℝ := ∫ x, weight a x ^ 2 ∂μ

theorem continuous_weight (a : ℝ) : Continuous (weight a) := by
  unfold weight
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
    (fun x => (Real.cosh_pos (a * x)).ne')

theorem measurable_weight (a : ℝ) : Measurable (weight a) :=
  (continuous_weight a).measurable

theorem weight_neg (a x : ℝ) : weight a (-x) = -weight a x := by
  simp [weight, Real.tanh_neg]

theorem abs_weight_lt_one (a x : ℝ) : |weight a x| < 1 :=
  Real.abs_tanh_lt_one _

theorem integrable_weight (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Integrable (weight a) μ := by
  refine Integrable.of_bound (measurable_weight a).aestronglyMeasurable 1 ?_
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using (abs_weight_lt_one a x).le)

theorem integrable_weight_sq (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Integrable (fun x => weight a x ^ 2) μ := by
  refine Integrable.of_bound ((measurable_weight a).pow_const 2).aestronglyMeasurable 1 ?_
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (weight a x))]
    exact (Real.tanh_sq_lt_one (a * x)).le)

/-- An odd measurable observable has zero expectation under a symmetric law. -/
theorem integral_odd_eq_zero (μ : Measure ℝ) (hμ : SymmetricLaw μ)
    (f : ℝ → ℝ) (hf : Measurable f) (hodd : ∀ x, f (-x) = -f x) :
    (∫ x, f x ∂μ) = 0 := by
  have h := integral_map (μ := μ) measurable_neg.aemeasurable hf.aestronglyMeasurable
  rw [show μ.map (fun x : ℝ => -x) = μ from hμ] at h
  simp_rw [hodd] at h
  rw [integral_neg] at h
  linarith

theorem weight_mean_zero (μ : Measure ℝ) (hμ : SymmetricLaw μ) (a : ℝ) :
    (∫ x, weight a x ∂μ) = 0 :=
  integral_odd_eq_zero μ hμ (weight a) (measurable_weight a) (weight_neg a)

theorem secondMoment_nonneg (μ : Measure ℝ) (a : ℝ) : 0 ≤ secondMoment μ a :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem secondMoment_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    secondMoment μ a ≤ 1 := by
  calc
    secondMoment μ a ≤ ∫ _ : ℝ, (1 : ℝ) ∂μ :=
      integral_mono (integrable_weight_sq μ a) (integrable_const 1)
        (fun x => (Real.tanh_sq_lt_one (a * x)).le)
    _ = 1 := by simp

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A disorder monomial indexed by an actual finite edge subset. -/
def monomial (a : E → ℝ) (S : Finset E) (J : E → ℝ) : ℝ :=
  ∏ e ∈ S, weight (a e) (J e)

theorem monomial_eq_full_prod (a : E → ℝ) (S : Finset E) (J : E → ℝ) :
    monomial a S J = ∏ e, if e ∈ S then weight (a e) (J e) else 1 := by
  simp [monomial]

omit [Fintype E] [DecidableEq E] in
theorem continuous_monomial (a : E → ℝ) (S : Finset E) : Continuous (monomial a S) := by
  unfold monomial
  exact continuous_finsetProd _ fun e _ => (continuous_weight (a e)).comp (continuous_apply e)

omit [Fintype E] [DecidableEq E] in
theorem abs_monomial_le_one (a : E → ℝ) (S : Finset E) (J : E → ℝ) :
    |monomial a S J| ≤ 1 := by
  rw [monomial, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun e _ => (abs_weight_lt_one _ _).le)

omit [DecidableEq E] in
theorem integrable_monomial (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : E → ℝ) (S : Finset E) : Integrable (monomial a S) (iidLaw μ) := by
  refine Integrable.of_bound (continuous_monomial a S).measurable.aestronglyMeasurable 1 ?_
  exact ae_of_all _ (fun J => by simpa only [Real.norm_eq_abs] using abs_monomial_le_one a S J)

omit [DecidableEq E] in
theorem integrable_monomial_mul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : E → ℝ) (S T : Finset E) :
    Integrable (fun J => monomial a S J * monomial a T J) (iidLaw μ) := by
  refine Integrable.of_bound
    ((continuous_monomial a S).mul (continuous_monomial a T)).measurable.aestronglyMeasurable 1 ?_
  refine ae_of_all _ (fun J => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [abs_monomial_le_one a S J, abs_monomial_le_one a T J,
    abs_nonneg (monomial a S J), abs_nonneg (monomial a T J)]

/-- Exact product-law factorization of the product of two graph monomials. -/
theorem monomial_pair_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : E → ℝ) (S T : Finset E) :
    (∫ J, monomial a S J * monomial a T J ∂iidLaw μ) =
      ∏ e, ∫ x, (if e ∈ S then weight (a e) x else 1) *
        (if e ∈ T then weight (a e) x else 1) ∂μ := by
  simp_rw [monomial_eq_full_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ : E => μ)
    (fun e x => (if e ∈ S then weight (a e) x else 1) *
      (if e ∈ T then weight (a e) x else 1))

/-- Orthogonality under the original arbitrary symmetric iid real disorder. -/
theorem monomial_orthogonality (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (a : E → ℝ) (S T : Finset E) :
    (∫ J, monomial a S J * monomial a T J ∂iidLaw μ) =
      if S = T then ∏ e ∈ S, secondMoment μ (a e) else 0 := by
  rw [monomial_pair_integral]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl, ← Finset.prod_ite_mem_eq S (fun e => secondMoment μ (a e))]
    apply Finset.prod_congr rfl
    intro e he
    by_cases heS : e ∈ S
    · simp only [heS, if_true, secondMoment, ← sq]
    · simp [heS]
  · rw [if_neg hST]
    obtain ⟨e, he⟩ : ∃ e, ¬(e ∈ S ↔ e ∈ T) := by
      by_contra h
      push Not at h
      exact hST (Finset.ext h)
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    by_cases heS : e ∈ S <;> by_cases heT : e ∈ T
    · exact False.elim (he (by simp [heS, heT]))
    · simpa [heS, heT] using weight_mean_zero μ hμ (a e)
    · simpa [heS, heT] using weight_mean_zero μ hμ (a e)
    · exact False.elim (he (by simp [heS, heT]))


/-- Exact Parseval identity for any deterministic family of graph coefficients,
under the original iid symmetric real disorder rather than a finite sign model. -/
theorem polynomial_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (a : E → ℝ)
    (A : Finset (Finset E)) (c : Finset E → ℝ) :
    (∫ J, (∑ S ∈ A, c S * monomial a S J) ^ 2 ∂iidLaw μ) =
      ∑ S ∈ A, c S ^ 2 * ∏ e ∈ S, secondMoment μ (a e) := by
  have hint (S T : Finset E) : Integrable
      (fun J => (c S * c T) * (monomial a S J * monomial a T J)) (iidLaw μ) :=
    (integrable_monomial_mul μ a S T).const_mul _
  calc
    _ = ∫ J, ∑ S ∈ A, ∑ T ∈ A,
        (c S * c T) * (monomial a S J * monomial a T J) ∂iidLaw μ := by
      congr 1
      funext J
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      ring
    _ = ∑ S ∈ A, ∑ T ∈ A, ∫ J,
        (c S * c T) * (monomial a S J * monomial a T J) ∂iidLaw μ := by
      rw [integral_finsetSum A (fun S _ => integrable_finsetSum A (fun T _ => hint S T))]
      apply Finset.sum_congr rfl
      intro S hS
      exact integral_finsetSum A (fun T _ => hint S T)
    _ = ∑ S ∈ A, ∑ T ∈ A, (c S * c T) *
        (if S = T then ∏ e ∈ S, secondMoment μ (a e) else 0) := by
      simp_rw [integral_const_mul, monomial_orthogonality μ hμ]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [mul_ite, hS, sq]

/-- An actual discarded graph family has exactly its second-moment mass. -/
theorem graph_family_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (a : ℝ) (A : Finset (Finset E)) :
    (∫ J, (∑ S ∈ A, monomial (fun _ => a) S J) ^ 2 ∂iidLaw μ) =
      ∑ S ∈ A, secondMoment μ a ^ S.card := by
  simpa using polynomial_second_moment μ hμ (fun _ => a) A (fun _ => 1)

/-- The exact error between an arbitrary polynomial and its retained terms. -/
theorem retained_polynomial_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (a : E → ℝ) (A : Finset (Finset E))
    (c : Finset E → ℝ) (keep : Finset E → Prop) [DecidablePred keep] :
    (∫ J, ((∑ S ∈ A, c S * monomial a S J) -
      (∑ S ∈ A.filter keep, c S * monomial a S J)) ^ 2 ∂iidLaw μ) =
      ∑ S ∈ A.filter (fun S => ¬keep S), c S ^ 2 * ∏ e ∈ S, secondMoment μ (a e) := by
  have heq (J : E → ℝ) :
      (∑ S ∈ A, c S * monomial a S J) -
        (∑ S ∈ A.filter keep, c S * monomial a S J) =
      ∑ S ∈ A, (if keep S then 0 else c S) * monomial a S J := by
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hS : keep S <;> simp [hS]
  simp_rw [heq]
  rw [polynomial_second_moment μ hμ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hS : keep S <;> simp [hS]

omit [DecidableEq E] in
/-- The iid assumption on an arbitrary probability space gives exactly the
canonical product law, so using `iidLaw` does not restrict the disorder model. -/
theorem iidLaw_of_independent_identical
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Measure ℝ) (J : E → Ω → ℝ)
    (hind : iIndepFun J P) (hmeas : ∀ e, AEMeasurable (J e) P)
    (hlaw : ∀ e, P.map (J e) = μ) :
    P.map (fun ω e => J e ω) = iidLaw μ := by
  rw [hind.map_fun_eq_pi_map hmeas]
  simp only [hlaw, iidLaw]

end SpinGlass.Disorder
