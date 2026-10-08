import SpinGlass.OrderedSK
import SpinGlass.PhysicalInput
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi

/-! The Section 9.2 transformation sends the actual iid ordered Gaussian matrix
to mutually independent standard Gaussian unordered couplings. -/
noncomputable section
namespace SpinGlass.OrderedSKGaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators

abbrev Upper (N : ℕ) := {q : Fin N × Fin N // q.1 < q.2}

def coordinate {N : ℕ} (p : Upper N × Bool) : Fin N × Fin N :=
  if p.2 then (p.1.val.2,p.1.val.1) else p.1.val

theorem coordinate_injective (N : ℕ) : Function.Injective (coordinate (N := N)) := by
  rintro ⟨p,b⟩ ⟨q,c⟩ he
  cases b <;> cases c
  · simp only [coordinate,Bool.false_eq_true,if_false] at he
    exact Prod.ext (Subtype.ext he) rfl
  · simp only [coordinate,Bool.false_eq_true,if_false,if_true] at he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    have hp := p.property
    rw [h1,h2] at hp
    exact False.elim (lt_asymm hp q.property)
  · simp only [coordinate,Bool.false_eq_true,if_false,if_true] at he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    have hq := q.property
    rw [←h1,←h2] at hq
    exact False.elim (lt_asymm hq p.property)
  · simp only [coordinate,if_true] at he
    have hpq : p=q := Subtype.ext (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))
    exact Prod.ext hpq rfl

def standard : Measure ℝ := gaussianReal 0 1
instance standard_probability : IsProbabilityMeasure standard := by unfold standard; infer_instance

def rawLaw (N : ℕ) : Measure (Fin N × Fin N → ℝ) :=
  Measure.infinitePi (fun _ => standard)

instance rawLaw_probability (N : ℕ) : IsProbabilityMeasure (rawLaw N) := by
  unfold rawLaw
  infer_instance

def grouped {N : ℕ} (G : Fin N × Fin N → ℝ) (e : Upper N) (b : Bool) : ℝ :=
  G (coordinate (e,b))

/-- All off-diagonal orientation pairs have the actual product law. This is
mutual independence, obtained by injective coordinate restriction and currying. -/
theorem grouped_law (N : ℕ) :
    (rawLaw N).map grouped =
      Measure.infinitePi (fun _ : Upper N => Measure.infinitePi (fun _ : Bool => standard)) := by
  have hi := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin N × Fin N => standard) (coordinate_injective N)
  calc
    (rawLaw N).map grouped =
      ((rawLaw N).map (fun (G : Fin N × Fin N → ℝ) (p : Upper N × Bool) => G (coordinate p))).map
        (MeasurableEquiv.curry (Upper N) Bool ℝ) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [show (rawLaw N).map (fun (G : Fin N × Fin N → ℝ) (p : Upper N × Bool) => G (coordinate p)) =
        Measure.infinitePi (fun _ : Upper N × Bool => standard) from hi]
      exact Measure.infinitePi_map_curry (fun _ : Upper N => fun _ : Bool => standard)

def mix (x : Bool → ℝ) : ℝ := (x false+x true)/Real.sqrt 2

/-- The average of the two independent unit-variance Gaussian orientations has
unit variance after division by sqrt 2. -/
theorem mix_law :
    (Measure.infinitePi (fun _ : Bool => standard)).map mix = standard := by
  let P := Measure.infinitePi (fun _ : Bool => standard)
  have hind : iIndepFun (fun b : Bool => fun x : Bool → ℝ => x b) P :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hs := gaussianReal_add_gaussianReal_of_indepFun
    (hind.indepFun (show false≠true by decide))
    (show P.map (fun x => x false)=gaussianReal 0 1 from Measure.infinitePi_map_eval _ false)
    (show P.map (fun x => x true)=gaussianReal 0 1 from Measure.infinitePi_map_eval _ true)
  have hsum : HasLaw (fun x : Bool → ℝ => x false+x true) (gaussianReal 0 2) P :=
    ⟨by fun_prop,by simpa only [Pi.add_apply,zero_add,one_add_one_eq_two,Pi.add_def] using hs⟩
  have hd := gaussianReal_div_const hsum (Real.sqrt 2)
  have hv : (2 : NNReal) / NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) = 1 := by
    ext
    simp [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  change P.map (fun x : Bool → ℝ => (x false+x true)/Real.sqrt 2) = gaussianReal 0 1
  simpa only [zero_div,hv] using hd.map_eq

def transformed {N : ℕ} (G : Fin N × Fin N → ℝ) (e : Upper N) : ℝ :=
  (G e.val+G (e.val.2,e.val.1))/Real.sqrt 2

/-- Exact joint law of every transformed coupling, not merely their marginals. -/
theorem transformed_joint_law (N : ℕ) :
    (rawLaw N).map transformed = Measure.infinitePi (fun _ : Upper N => standard) := by
  calc
    (rawLaw N).map transformed = ((rawLaw N).map grouped).map (fun x e => mix (x e)) := by
      rw [Measure.map_map (by unfold mix; fun_prop) (by unfold grouped; fun_prop)]
      rfl
    _ = _ := by
      rw [grouped_law,Measure.infinitePi_map_pi _ (fun _ => by unfold mix; fun_prop)]
      simp_rw [mix_law]

/-- The exact transformed variables are mutually independent standard Gaussians. -/
theorem transformed_independent (N : ℕ) :
    iIndepFun (fun e : Upper N => fun G => transformed G e) (rawLaw N) := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (by intro e; unfold transformed; fun_prop)).mpr
  rw [transformed_joint_law]
  congr 1
  funext e
  have h := congrArg (fun μ : Measure (Upper N → ℝ) => μ.map (fun x => x e)) (transformed_joint_law N)
  rw [Measure.map_map (by fun_prop) (by unfold transformed; fun_prop),
    Measure.infinitePi_map_eval] at h
  exact h.symm

theorem transformed_marginal (N : ℕ) (e : Upper N) :
    (rawLaw N).map (fun G => transformed G e) = standard := by
  have h := congrArg (fun μ : Measure (Upper N → ℝ) => μ.map (fun x => x e)) (transformed_joint_law N)
  rw [Measure.map_map (by fun_prop) (by unfold transformed; fun_prop),
    Measure.infinitePi_map_eval] at h
  exact h

/-- The joint-law variables coincide with the unordered couplings used in (95). -/
theorem transformed_eq_coupling {N : ℕ} (G : Fin N × Fin N → ℝ) (e : Upper N) :
    transformed G e = OrderedSK.coupling G (OrderedSK.pairEdge e.val) := by
  rw [OrderedSK.coupling_pair G (by simpa [OrderedSK.upperPairs] using e.property)]
  rfl

theorem rawLaw_eq_iidLaw (N : ℕ) : rawLaw N=SpinGlass.Disorder.iidLaw standard := by
  exact Measure.infinitePi_eq_pi _

theorem standard_symmetric : SpinGlass.Disorder.SymmetricLaw standard := by
  simpa [SpinGlass.Disorder.SymmetricLaw,standard] using
    (gaussianReal_map_neg (μ := 0) (v := 1))

theorem standard_unit_second_moment : SpinGlass.Disorder.UnitSecondMoment standard := by
  have hLp : MemLp (id : ℝ → ℝ) 2 standard := memLp_id_gaussianReal (2 : NNReal)
  constructor
  · simpa only [Real.norm_eq_abs,id_eq,sq_abs] using hLp.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  · have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral (by fun_prop)] at h
    simpa [standard] using h

theorem standard_fourth_moment : Integrable (fun x : ℝ => |x|^4) standard := by
  have hLp : MemLp (id : ℝ → ℝ) 4 standard := memLp_id_gaussianReal (4 : NNReal)
  simpa only [Real.norm_eq_abs,id_eq] using hLp.integrable_norm_pow (by norm_num : (4:ℕ)≠0)

def upperEdge {N : ℕ} (q : Upper N) : PhysicalInput.Edge (Fin N) 2 :=
  ⟨OrderedSK.pairEdge q.val, by
    rw [←OrderedSK.upperPairs_image]
    exact Finset.mem_image.mpr ⟨q.val,by simpa [OrderedSK.upperPairs] using q.property,rfl⟩⟩

theorem upperEdge_bijective (N : ℕ) : Function.Bijective (upperEdge (N := N)) := by
  constructor
  · intro q r h
    apply Subtype.ext
    apply OrderedSK.pairEdge_injOn N
    · simpa [OrderedSK.upperPairs] using q.property
    · simpa [OrderedSK.upperPairs] using r.property
    · exact congrArg Subtype.val h
  · intro e
    have he : e.val ∈ (OrderedSK.upperPairs N).image OrderedSK.pairEdge := by
      simpa only [OrderedSK.upperPairs_image] using e.property
    rcases Finset.mem_image.mp he with ⟨q,hq,he⟩
    refine ⟨⟨q,by simpa [OrderedSK.upperPairs] using hq⟩,?_⟩
    exact Subtype.ext he

def edgeEquiv (N : ℕ) : Upper N ≃ PhysicalInput.Edge (Fin N) 2 :=
  Equiv.ofBijective upperEdge (upperEdge_bijective N)

/-- The physical input array contains exactly the unordered two-element edges. -/
def physicalCoupling {N : ℕ} (G : Fin N × Fin N → ℝ) : PhysicalInput.Edge (Fin N) 2 → ℝ :=
  PhysicalInput.restrict 2 (OrderedSK.coupling G)

theorem physicalCoupling_eq {N : ℕ} (G : Fin N × Fin N → ℝ) :
    physicalCoupling G = fun e => transformed G ((edgeEquiv N).symm e) := by
  funext e
  rw [transformed_eq_coupling]
  have he := congrArg Subtype.val ((edgeEquiv N).apply_symm_apply e)
  change OrderedSK.pairEdge ((edgeEquiv N).symm e).val=e.val at he
  simp only [physicalCoupling,PhysicalInput.restrict,he]

theorem measurable_physicalCoupling (N : ℕ) : Measurable (physicalCoupling (N := N)) := by
  have heq : physicalCoupling (N := N) =
      fun G e => transformed G ((edgeEquiv N).symm e) := funext physicalCoupling_eq
  rw [heq]
  unfold transformed
  fun_prop

/-- Direct iid law on precisely the input edge type of the certified SK algorithm. -/
theorem physical_joint_law (N : ℕ) :
    (rawLaw N).map physicalCoupling = Disorder.iidLaw (E := PhysicalInput.Edge (Fin N) 2) standard := by
  calc
    (rawLaw N).map physicalCoupling =
        ((rawLaw N).map transformed).map (fun x e => x ((edgeEquiv N).symm e)) := by
      rw [Measure.map_map (by fun_prop) (by unfold transformed; fun_prop)]
      congr 1
      funext G
      exact physicalCoupling_eq G
    _ = _ := by
      rw [transformed_joint_law]
      rw [Measure.map_infinitePi_infinitePi_of_inj ((edgeEquiv N).symm.injective)]
      exact Measure.infinitePi_eq_pi _

/-- External algorithm coins remain independent after Gaussian normalization. -/
theorem physical_joint_law_with_coins {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (N : ℕ) :
    (P.prod (rawLaw N)).map (Prod.map id physicalCoupling) =
      P.prod (Disorder.iidLaw (E := PhysicalInput.Edge (Fin N) 2) standard) := by
  have hp : MeasurePreserving (physicalCoupling (N := N)) (rawLaw N)
      (Disorder.iidLaw standard) := ⟨measurable_physicalCoupling N,physical_joint_law N⟩
  exact ((MeasurePreserving.id P).prod hp).map_eq

/-- Exact event-probability transfer, ready to apply to the physical-input
algorithm theorem. There is no independent-coordinate assumption to discharge. -/
theorem event_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (N : ℕ)
    (S : Set (Ω × (PhysicalInput.Edge (Fin N) 2 → ℝ))) (hS : MeasurableSet S) :
    (P.prod (rawLaw N)).real {ωG | (ωG.1,physicalCoupling ωG.2)∈S} =
      (P.prod (Disorder.iidLaw standard)).real S := by
  rw [←physical_joint_law_with_coins P N]
  unfold Measure.real
  rw [Measure.map_apply (measurable_id.prodMap (measurable_physicalCoupling N)) hS]
  rfl

end SpinGlass.OrderedSKGaussian
