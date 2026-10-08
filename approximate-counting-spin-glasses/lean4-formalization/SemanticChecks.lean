import SpinGlass.MainCorollaries
import SpinGlass.Threshold
import SpinGlass.PhysicalInputTheorems
import SpinGlass.ConditionalSuccess
import SpinGlass.OrderedSKGaussian
import SpinGlass.OrderedSKPreparation

#check SpinGlass.ConditionalSpinGlass.normalizedPartition_eq_graphPolynomial
#check SpinGlass.ConditionalSpinGlass.normalizedPartition_negative_moment
#check SpinGlass.ConditionalSpinGlass.normalizedPartition_lower_tail
#check SpinGlass.RandomCoefficient.polynomial_error_second_moment
#check SpinGlass.RandomCoefficient.integrated_polynomial_error_second_moment
#check SpinGlass.RandomCoefficient.retained_family_error

#print axioms SpinGlass.ConditionalSpinGlass.normalizedPartition_eq_graphPolynomial
#print axioms SpinGlass.ConditionalSpinGlass.normalizedPartition_negative_moment
#print axioms SpinGlass.ConditionalSpinGlass.normalizedPartition_lower_tail
#print axioms SpinGlass.RandomCoefficient.polynomial_error_second_moment
#print axioms SpinGlass.RandomCoefficient.integrated_polynomial_error_second_moment
#print axioms SpinGlass.RandomCoefficient.retained_family_error

open SpinGlass.ConditionalSpinGlass SpinGlass.Expansion SpinGlass.Partition

section EmptyEdges
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

example (incidence : E → Finset V) (b : E → ℝ) (η : E → Bool) :
    graphPolynomial incidence ∅ b η = 1 := by
  simp [graphPolynomial, evenGraphs, Finset.filter_singleton, IsEven, degree, spinCharacter]

example (incidence : E → Finset V) (b : E → ℝ) (θ : ℝ) :
    inflatedMass incidence ∅ θ b = 1 := by
  simp [inflatedMass, evenGraphs, Finset.filter_singleton, IsEven, degree]

example (incidence : E → Finset V) (x : E → ℝ) :
    normalizedPartition incidence ∅ x = 1 := by
  rw [normalizedPartition_eq_even_sum]
  simp [Finset.filter_singleton, IsEven, degree]

example (c d : Finset E → ℝ) :
    spinMean (fun η : E → Bool =>
      ((∑ Γ ∈ (∅ : Finset (Finset E)), c Γ * spinCharacter Γ η) -
        (∑ Γ ∈ (∅ : Finset (Finset E)), d Γ * spinCharacter Γ η)) ^ 2) = 0 := by
  simpa using SpinGlass.RandomCoefficient.polynomial_error_second_moment ∅ c d

end EmptyEdges


-- The complete statements expose all assumptions, including the remainder.
#check SpinGlass.HigherOrderTotalCost.end_to_end
#check SpinGlass.SKTotalCost.end_to_end
#print axioms SpinGlass.HigherOrderTotalCost.end_to_end
#print axioms SpinGlass.SKTotalCost.end_to_end
#print axioms SpinGlass.MainCorollaries.higher_fourth_end_to_end
#print axioms SpinGlass.MainCorollaries.higher_real_moment_end_to_end

-- Parity is retained beyond degree four; odd degree five is not accepted as four.
example : SpinGlass.rho 6 = 4 ∧ SpinGlass.rho 7 = 5 := by decide
example : SpinGlass.rho 100 = 4 ∧ SpinGlass.rho 101 = 5 := by decide

-- The SK temperature threshold and the zero-temperature partition normalization.
example : SpinGlass.UniformMassEntropy.thresholdSquared 2 = 1 :=
  SpinGlass.Threshold.thresholdSquared_two

example (p N : ℕ) (J : Finset (Fin N) → ℝ) :
    SpinGlass.CountingReduction.targetLog p N 0 J = N*Real.log 2 := by
  simp [SpinGlass.CountingReduction.targetLog, SpinGlass.Partition.partitionFunction,
    SpinGlass.Disorder.pureScale, Real.log_pow]

#print axioms SpinGlass.MainCorollaries.sk_fourth_end_to_end
#print axioms SpinGlass.MainCorollaries.sk_real_moment_end_to_end

-- The admissible SK temperature interval is nonempty, not a vacuous premise.
example : (1/2:ℝ) < SpinGlass.DesignConstants.betaThreshold 2 := by
  norm_num [SpinGlass.DesignConstants.betaThreshold, SpinGlass.Threshold.thresholdSquared_two]

#check SpinGlass.PhysicalInput.higher_end_to_end
#check SpinGlass.PhysicalInput.sk_end_to_end
#print axioms SpinGlass.PhysicalInput.higher_end_to_end
#print axioms SpinGlass.PhysicalInput.sk_end_to_end
#print axioms SpinGlass.ConditionalSuccess.sk_conditional_remainder
#print axioms SpinGlass.OrderedSKGaussian.transformed_joint_law
#print axioms SpinGlass.OrderedSKPreparation.prepare_operations

#print axioms SpinGlass.OrderedSKGaussian.physical_joint_law_with_coins
#print axioms SpinGlass.OrderedSKPreparation.transformation_operations
#print axioms SpinGlass.OrderedSKPreparation.finish_error
