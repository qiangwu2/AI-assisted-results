import SpinGlass.DisorderRestriction
import SpinGlass.InputPreparation

/-! Exact input adapter from actual p-edges to the ambient bookkeeping array. -/
noncomputable section
namespace SpinGlass.PhysicalInput
open MeasureTheory
open scoped BigOperators
open SpinGlass.Disorder SpinGlass.InputPreparation
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Edge (V : Type*) [Fintype V] [DecidableEq V] (p : ℕ) :=
  {e : Finset V // e ∈ (Finset.univ : Finset V).powersetCard p}

def extend (p : ℕ) (J : Edge V p → ℝ) : Finset V → ℝ :=
  fun e => if h : e ∈ (Finset.univ : Finset V).powersetCard p then J ⟨e,h⟩ else 0

def restrict (p : ℕ) (J : Finset V → ℝ) : Edge V p → ℝ := fun e => J e

@[simp] theorem extend_edge (p : ℕ) (J : Edge V p → ℝ) (e : Edge V p) :
    extend p J e = J e := by simp [extend,e.property]

@[simp] theorem restrict_extend (p : ℕ) (J : Edge V p → ℝ) :
    restrict p (extend p J) = J := by funext e; simp [restrict]

@[simp] theorem extend_restrict_edge (p : ℕ) (J : Finset V → ℝ)
    {e : Finset V} (he : e ∈ (Finset.univ : Finset V).powersetCard p) :
    extend p (restrict p J) e = J e := by simp [extend,restrict,he]

theorem measurable_extend (p : ℕ) : Measurable (extend (V := V) p) := by
  apply measurable_pi_lambda
  intro e
  unfold extend
  split_ifs <;> fun_prop

theorem prepareEdges_congr {E : Type*} (a : ℝ) (J K : E → ℝ) (es : List E)
    (h : ∀ e ∈ es, J e = K e) : prepareEdges a J es = prepareEdges a K es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [prepareEdges, h e (by simp), ih (fun e he => h e (by simp [he]))]

/-- The entire cached input, including every cost and prefactor field, depends
only on actual physical edges. -/
theorem prepareInput_congr (p : ℕ) (beta : ℝ) (J K : Finset V → ℝ)
    (h : ∀ e ∈ (Finset.univ : Finset V).powersetCard p, J e = K e) :
    prepareInput p beta J = prepareInput p beta K := by
  have he := prepareEdges_congr (scaleComputation (Fintype.card V) p beta).value J K
    ((Finset.univ : Finset V).powersetCard p).toList (fun e he => h e (by simpa using he))
  simp only [prepareInput,he]

@[simp] theorem prepareInput_extend_restrict (p : ℕ) (beta : ℝ) (J : Finset V → ℝ) :
    prepareInput p beta (extend p (restrict p J)) = prepareInput p beta J :=
  prepareInput_congr p beta _ _ (fun e he => extend_restrict_edge p J he)

/-- Exact product-law marginal on the physical input coordinates. -/
theorem restrict_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℕ) :
    (iidLaw (E := Finset V) μ).map (restrict p) = iidLaw (E := Edge V p) μ :=
  iidLaw_restrict μ Subtype.val Subtype.val_injective

/-- Random algorithm coins remain independent of the physical disorder inputs. -/
theorem restrict_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℕ) :
    (P.prod (iidLaw (E := Finset V) μ)).map (Prod.map id (restrict p)) =
      P.prod (iidLaw (E := Edge V p) μ) := by
  have hr : MeasurePreserving (restrict (V := V) p) (iidLaw (E := Finset V) μ)
      (iidLaw (E := Edge V p) μ) :=
    ⟨measurable_restrictArray Subtype.val, restrict_law μ p⟩
  exact ((MeasurePreserving.id P).prod hr).map_eq

/-- A physical-input error event has exactly the probability of its ambient
bookkeeping version, provided the latter reads only physical coordinates. -/
theorem event_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℕ)
    (S : Set (Ω × (Finset V → ℝ))) (hS : MeasurableSet S)
    (hread : ∀ ω J, (ω,extend p (restrict p J)) ∈ S ↔ (ω,J) ∈ S) :
    (P.prod (iidLaw (E := Edge V p) μ)).real
      {ωJ | (ωJ.1, extend p ωJ.2) ∈ S} = (P.prod (iidLaw (E := Finset V) μ)).real S := by
  rw [← restrict_joint_law P μ p]
  unfold Measure.real
  have hm : Measurable (Prod.map (id : Ω → Ω) (restrict (V := V) p)) :=
    measurable_id.prodMap (measurable_restrictArray Subtype.val)
  have hs : MeasurableSet {ωJ : Ω × (Edge V p → ℝ) | (ωJ.1, extend p ωJ.2) ∈ S} :=
    hS.preimage (measurable_id.prodMap (measurable_extend p))
  rw [Measure.map_apply hm hs]
  have heq : (Prod.map (id : Ω → Ω) (restrict (V := V) p)) ⁻¹'
      {ωJ : Ω × (Edge V p → ℝ) | (ωJ.1, extend p ωJ.2) ∈ S} = S := by
    ext ωJ
    exact hread ωJ.1 ωJ.2
  rw [heq]

/-- The deterministic version of the same exact probability transport. -/
theorem event_probability_single (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℕ)
    (S : Set (Finset V → ℝ)) (hS : MeasurableSet S)
    (hread : ∀ J, extend p (restrict p J) ∈ S ↔ J ∈ S) :
    (iidLaw (E := Edge V p) μ).real {J | extend p J ∈ S} =
      (iidLaw (E := Finset V) μ).real S := by
  rw [← restrict_law μ p]
  unfold Measure.real
  have hm : Measurable (restrict (V := V) p) := measurable_restrictArray Subtype.val
  have hs : MeasurableSet {J : Edge V p → ℝ | extend p J ∈ S} := hS.preimage (measurable_extend p)
  rw [Measure.map_apply hm hs]
  have heq : (restrict (V := V) p) ⁻¹' {J : Edge V p → ℝ | extend p J ∈ S} = S := by
    ext J
    exact hread J
  rw [heq]

end SpinGlass.PhysicalInput
