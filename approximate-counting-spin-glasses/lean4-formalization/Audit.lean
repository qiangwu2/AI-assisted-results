import SpinGlass
import Lean.Util.CollectAxioms

/-!
This audit requires the final accuracy-and-total-cost endpoints and rejects every
nonstandard axiom dependency in every SpinGlass declaration, including private
declarations, sorryAx, and compiler-trust axioms. See COVERAGE.md for the encoded scope.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    ``SpinGlass.rho_add_left,
    ``SpinGlass.Hypergraph.twice_support_le_uniform_edge_count,
    ``SpinGlass.ColorSupport.prod_eq_none_at_L_succ,
    ``SpinGlass.Expansion.graphical_expansion,
    ``SpinGlass.Expansion.edge_subset_second_moment,
    ``SpinGlass.Mobius.transform_Gspin_eq_exact_support,
    ``SpinGlass.Partition.normalizedPartition_eq_even_sum,
    ``SpinGlass.LowerTail.moment_interpolation,
    ``SpinGlass.Noise.cubeNoise_inflated_polynomial,
    ``SpinGlass.logOutput_probability,
    ``SpinGlass.logOutput_probability_with_paper_parameters,
    ``SpinGlass.ReverseHypercontractivityIngredients.curvature_comparison,
    ``SpinGlass.ReverseHypercontractivityTwoPoint.homogeneous_two_point_sq,
    ``SpinGlass.Tensorization.bool_cube_reverse_bound_fintype,
    ``SpinGlass.ReverseHolder.negative_moment_of_bilinear,
    ``SpinGlass.NoiseKernel.jointKernel_bilinear_eq_reverse,
    ``SpinGlass.NoiseMomentReduction.negative_moment_of_cube_bilinear,
    ``SpinGlass.BilinearTwoPoint.bit_reverse_bound,
    ``SpinGlass.ReverseHypercontractivity.negative_moment,
    ``SpinGlass.ReverseHypercontractivity.reverse_norm,
    ``SpinGlass.FiniteLowerTail.noisy_lower_tail_le_second_moment,
    ``SpinGlass.ConditionalSpinGlass.normalizedPartition_negative_moment,
    ``SpinGlass.ConditionalSpinGlass.normalizedPartition_lower_tail,
    ``SpinGlass.LocalCube.Gspin_eq_localGspin,
    ``SpinGlass.RandomCoefficient.integrated_polynomial_error_second_moment,
    ``SpinGlass.RandomCoefficient.retained_family_error,
    ``SpinGlass.GraphicalMass.sign_second_moment_eq_spinMean,
    ``SpinGlass.GraphicalMass.pure_p_spin_mass_le_exp_moment,
    ``SpinGlass.UniformMass.uniform_graphical_mass,
    ``SpinGlass.Threshold.thresholdSquared_two,
    ``SpinGlass.Disorder.normalizedPartition_lower_tail_iid,
    ``SpinGlass.SKCoefficientCorrectness.estimator_eq_disorder,
    ``SpinGlass.SKUniformAlgorithm.mean_square,
    ``SpinGlass.SKUniformAlgorithm.fast_mean_square,
    ``SpinGlass.SKCountedExecution.generatedEstimator_value,
    ``SpinGlass.SKCountedExecution.generatedEstimator_operations_le,
    ``SpinGlass.RoundingExecution.all_rounding_operations,
    ``SpinGlass.HigherOrderTotalCost.end_to_end,
    ``SpinGlass.SKTotalCost.end_to_end,
    ``SpinGlass.MainCorollaries.higher_fourth_end_to_end,
    ``SpinGlass.MainCorollaries.higher_real_moment_end_to_end,
    ``SpinGlass.MainCorollaries.sk_fourth_end_to_end,
    ``SpinGlass.MainCorollaries.sk_real_moment_end_to_end,
    ``SpinGlass.Disorder.pure_remainder_eventually_zero_of_bounded,
    ``SpinGlass.PhysicalInput.sk_end_to_end,
    ``SpinGlass.PhysicalInput.higher_end_to_end,
    ``SpinGlass.SKLazySampling.restrict_joint_law,
    ``SpinGlass.SKLazySampling.generatedEstimator_complete,
    ``SpinGlass.SKLazySampling.queryList_nodup,
    ``SpinGlass.OrderedSK.logarithmic_error_preserved,
    ``SpinGlass.OrderedSKGaussian.transformed_joint_law,
    ``SpinGlass.OrderedSKPreparation.prepare_operations,
    ``SpinGlass.ConditionalSuccess.sk_conditional_remainder,
    ``SpinGlass.OrderedSKGaussian.physical_joint_law,
    ``SpinGlass.OrderedSKGaussian.physical_joint_law_with_coins,
    ``SpinGlass.OrderedSKGaussian.event_probability,
    ``SpinGlass.OrderedSKGaussian.standard_symmetric,
    ``SpinGlass.OrderedSKGaussian.standard_unit_second_moment,
    ``SpinGlass.OrderedSKGaussian.standard_fourth_moment,
    ``SpinGlass.OrderedSKPreparation.prepare_keys_nodup,
    ``SpinGlass.OrderedSKPreparation.transformation_operations,
    ``SpinGlass.OrderedSKPreparation.finish_error]
  for name in required do
    unless (env.find? name).any (fun ci => ci.isTheorem) do
      throwError "Missing required theorem endpoint {name}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theoremCount : Nat := 0
  let mut checkedCount : Nat := 0
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let userName := (privateToUserName? name).getD name
    if (`SpinGlass).isPrefixOf userName then
      names := names.push name
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name}"
    checkedCount := checkedCount + 1
    if let some (.thmInfo _) := env.find? name then
      theoremCount := theoremCount + 1
      logInfo m!"CHECKED {name}; axioms = {axioms.toList}"
  unless theoremCount > 0 do
    throwError "No SpinGlass theorems found"
  logInfo m!"AXIOM AUDIT PASSED: {theoremCount} theorem declarations; {checkedCount} total declarations."
  logInfo "STATUS: FINAL TOTAL-COST ENDPOINTS VERIFIED FOR BOTH p >= 3 AND SK p = 2."
