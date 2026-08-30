import StressTensor

/- `#print axioms` reports logical primitives used transitively through
Mathlib.  These checks document that the representative top-level results use
only Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`,
not a project-defined mathematical assumption. -/
#print axioms StressTensor.Params.ofP
#print axioms StressTensor.areaGradient_quarterTurn
#print axioms StressTensor.ae_hasDerivAt_candidateV_y
#print axioms StressTensor.singularStressDivergence_eq_zero_of_auxiliaryEquation
#print axioms StressTensor.candidateV_lower_growth
#print axioms StressTensor.candidateV_not_lipschitzNearAt_of_segment_bounds
#print axioms StressTensor.candidateGradient_inWeakLp_iff
#print axioms StressTensor.areaFunctional_le_of_calibration
#print axioms StressTensor.sectionFour_endpoint_duality
