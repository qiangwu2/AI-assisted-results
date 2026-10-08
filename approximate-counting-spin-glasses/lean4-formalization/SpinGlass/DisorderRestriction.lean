import SpinGlass.DisorderLowerTail

/-! Exact passage from an ambient finite iid array to the actual input edge subtype. -/
noncomputable section
namespace SpinGlass.Disorder
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {E F : Type*} [Fintype E] [Fintype F]

/-- Read only the coordinates named by an injective edge index map. -/
def restrictArray (i : F → E) (J : E → ℝ) : F → ℝ := fun e => J (i e)

theorem measurable_restrictArray (i : F → E) : Measurable (restrictArray i) :=
  measurable_pi_lambda _ fun e => measurable_pi_apply (i e)

/-- Discarding unused coordinates gives exactly the product law on the retained
input indices. No symmetry or moment assumption is needed for this fact. -/
theorem iidLaw_restrict (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (i : F → E) (hi : Function.Injective i) :
    (iidLaw (E := E) μ).map (restrictArray i) = iidLaw (E := F) μ := by
  have hind : iIndepFun (fun e : E => fun J : E → ℝ => J e) (iidLaw μ) :=
    iIndepFun_pi (μ := fun _ : E => μ) (X := fun _ : E => id)
      (fun _ => measurable_id.aemeasurable)
  apply iidLaw_of_independent_identical (iidLaw (E := E) μ) μ
      (fun e J => J (i e)) (hind.precomp hi)
      (fun e => (measurable_pi_apply (i e)).aemeasurable)
  intro e
  exact (measurePreserving_eval (fun _ : E => μ) (i e)).map_eq

/-- Every measurable observable has the same law under actual retained inputs. -/
theorem iidLaw_restrict_observable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (i : F → E) (hi : Function.Injective i) (f : (F → ℝ) → Y) (hf : Measurable f) :
    (iidLaw (E := E) μ).map (fun J => f (restrictArray i J)) =
      (iidLaw (E := F) μ).map f := by
  change (iidLaw (E := E) μ).map (f ∘ restrictArray i) = _
  rw [← Measure.map_map hf (measurable_restrictArray i), iidLaw_restrict μ i hi]

/-- Probability of every measurable retained-coordinate event is preserved. -/
theorem iidLaw_restrict_event (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (i : F → E) (hi : Function.Injective i) (S : Set (F → ℝ)) (hS : MeasurableSet S) :
    (iidLaw (E := E) μ).real (restrictArray i ⁻¹' S) =
      (iidLaw (E := F) μ).real S := by
  unfold Measure.real
  rw [← iidLaw_restrict μ i hi, Measure.map_apply (measurable_restrictArray i) hS]

/-- Integrals of measurable observables pass to the exact retained-coordinate law. -/
theorem iidLaw_restrict_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (i : F → E) (hi : Function.Injective i) (f : (F → ℝ) → ℝ) (hf : Measurable f) :
    (∫ J, f (restrictArray i J) ∂iidLaw (E := E) μ) =
      ∫ J, f J ∂iidLaw (E := F) μ := by
  rw [← iidLaw_restrict μ i hi]
  exact (integral_map (measurable_restrictArray i).aemeasurable hf.aestronglyMeasurable).symm

section ActualEdges
variable {V : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- The finite exponential partition function reads only actual edges. -/
theorem partitionFunction_restrict (incidence : E → Finset V) (edges : Finset E)
    (x : E → ℝ) :
    SpinGlass.Partition.partitionFunction incidence edges x =
      SpinGlass.Partition.partitionFunction (fun e : edges => incidence e)
        Finset.univ (fun e : edges => x e) := by
  unfold SpinGlass.Partition.partitionFunction
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  exact Finset.sum_subtype edges (fun _ => Iff.rfl) _

/-- The explicit product prefactor also reads only actual edges. -/
theorem prefactor_restrict (edges : Finset E) (x : E → ℝ) :
    SpinGlass.Partition.prefactor (V := V) edges x =
      SpinGlass.Partition.prefactor (V := V) Finset.univ (fun e : edges => x e) := by
  unfold SpinGlass.Partition.prefactor
  congr 1
  exact Finset.prod_subtype edges (fun _ => Iff.rfl) _

/-- Exact observable equivalence, for every disorder array, without an a.e. qualifier. -/
theorem normalizedPartition_restrict (incidence : E → Finset V) (edges : Finset E)
    (x : E → ℝ) :
    SpinGlass.Partition.normalizedPartition incidence edges x =
      SpinGlass.Partition.normalizedPartition (fun e : edges => incidence e)
        Finset.univ (fun e : edges => x e) := by
  unfold SpinGlass.Partition.normalizedPartition
  rw [partitionFunction_restrict, prefactor_restrict]

/-- The actual edge-input normalized partition has precisely the law used in the
ambient-coordinate theorems, including when edges is a p-uniform edge set. -/
theorem normalizedPartition_restrict_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (incidence : E → Finset V) (edges : Finset E) (a : E → ℝ) :
    (iidLaw (E := E) μ).map (fun J =>
      SpinGlass.Partition.normalizedPartition incidence edges (fun e => a e * J e)) =
    (iidLaw (E := edges) μ).map (fun J =>
      SpinGlass.Partition.normalizedPartition (fun e : edges => incidence e)
        Finset.univ (fun e : edges => a e * J e)) := by
  have hm : Measurable (fun J : edges → ℝ =>
      SpinGlass.Partition.normalizedPartition (fun e : edges => incidence e)
        Finset.univ (fun e : edges => a e * J e)) := by
    have hfun : (fun J : edges → ℝ =>
        SpinGlass.Partition.normalizedPartition (fun e : edges => incidence e)
          Finset.univ (fun e : edges => a e * J e)) =
        normalizedGraph (fun e : edges => incidence e) Finset.univ (fun e : edges => a e) := by
      funext J
      exact (normalizedGraph_eq_normalizedPartition _ _ _ _).symm
    rw [hfun]
    exact (continuous_normalizedGraph (fun e : edges => incidence e)
        Finset.univ (fun e : edges => a e)).measurable
  convert iidLaw_restrict_observable μ (fun e : edges => (e : E)) Subtype.val_injective
    _ hm using 1
  congr 1
  funext J
  exact normalizedPartition_restrict incidence edges _

end ActualEdges
end SpinGlass.Disorder
