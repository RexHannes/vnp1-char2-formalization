/-
# Axiom audit, support-two layer

`#print axioms` for every principal theorem added by the support-two layer.  The expected
(and observed) output is the standard Mathlib foundation `propext`, `Classical.choice`,
`Quot.sound`.  No project-specific axiom is declared anywhere in `VNP1Char2`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevelTwo
import RequestProject.AlgebraicComplexity.VNP1Char2.RegressionTestsTwo
import RequestProject.AlgebraicComplexity.VNP1Char2.SharpConstants
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevelAudit

namespace VNP1Char2

/-! ## Non-vacuity -/

/-- The support-two class theorem applies to a concrete family (`x₀`, in one variable for
every `n`), so the statement is not vacuous. -/
theorem sampleFamily_mem_VNP1LE2 {F : Type} [Field F] [CharP F 2] {τ : F} (hτ0 : τ ≠ 0)
    (hτ1 : τ ≠ 1) : VNP1LE2 (sampleFamily F) :=
  VPe_subset_VNP1LE2 hτ0 hτ1 sampleFamily_mem_VPe

/-- …and it is also a width-one-ABP hypercube family in the literature sense. -/
theorem sampleFamily_mem_VNP1BIZ {F : Type} [Field F] [CharP F 2] {τ : F} (hτ0 : τ ≠ 0)
    (hτ1 : τ ≠ 1) : VNP1BIZ (sampleFamily F) :=
  VNP1LE2_subset_VNP1BIZ (sampleFamily_mem_VNP1LE2 hτ0 hτ1)

/-! ## Axiom audit -/

-- The two characteristic-two identities, and the legality of the denominator `κ`.
#print axioms VNP1Char2.twoFactor_identity_denominator_free
#print axioms VNP1Char2.ternFactor_identity_denominator_free
#print axioms VNP1Char2.kappa_ne_zero
#print axioms VNP1Char2.twoFactor_identity
#print axioms VNP1Char2.ternFactor_identity
#print axioms VNP1Char2.twoFactorSum_mvPolynomial
#print axioms VNP1Char2.ternFactorSum_mvPolynomial
#print axioms VNP1Char2.cubic_error_not_formally_zero

-- The gadgets as lists of affine forms.
#print axioms VNP1Char2.sum_prod_gadget2Factors
#print axioms VNP1Char2.sum_prod_ternFactors
#print axioms VNP1Char2.numVars_ternFactors_le

-- The generic support-two compiler: flattening, error killing, value, support, size.
#print axioms VNP1Char2.prod_sum_flatten_one
#print axioms VNP1Char2.sum_cube3
#print axioms VNP1Char2.prod_add_err_mul
#print axioms VNP1Char2.compiled2_value_raw
#print axioms VNP1Char2.compiled2_value
#print axioms VNP1Char2.compiled2.supportLE_two
#print axioms VNP1Char2.compiled2.numAux_eq
#print axioms VNP1Char2.compiled2.numFactors_eq

-- The graph-level support-two compiler.
#print axioms VNP1Char2.PathGraph.exists_ternTriple
#print axioms VNP1Char2.PathGraph.tern_error_kill
#print axioms VNP1Char2.PathGraph.graphRep2_value
#print axioms VNP1Char2.PathGraph.graphRep2_supportLE_two
#print axioms VNP1Char2.PathGraph.graphRep2_numAux
#print axioms VNP1Char2.PathGraph.graphRep2_numFactors

-- The main finite support-two compiler theorem.
#print axioms VNP1Char2.Formula.rep2_value
#print axioms VNP1Char2.Formula.rep2_supportLE_two
#print axioms VNP1Char2.Formula.rep2_numAux_le
#print axioms VNP1Char2.Formula.rep2_numFactors_le
#print axioms VNP1Char2.Formula.has_supportTwo_affineHypercubeRepresentation
#print axioms VNP1Char2.Formula.has_supportTwo_representation_of_exists_tau

-- The sharp pair count and the sharp size bounds.
#print axioms VNP1Char2.Formula.toDag_numPairs
#print axioms VNP1Char2.Formula.rep2_numAux_le_sharp
#print axioms VNP1Char2.Formula.rep2_numFactors_le_sharp
#print axioms VNP1Char2.Formula.has_supportTwo_representation_sharp

-- The class level and the width-one-ABP literature bridge.
#print axioms VNP1Char2.nondetVPe_subset_VNP1LE2
#print axioms VNP1Char2.VPe_subset_VNP1LE2
#print axioms VNP1Char2.VNP1LE2_subset_nondetVPe
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE2
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE2_of_exists_tau
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE2_of_natCard
#print axioms VNP1Char2.VNP1LE2_subset_VNP1BIZ
#print axioms VNP1Char2.nondetVPe_subset_VNP1BIZ

-- Non-vacuity.
#print axioms VNP1Char2.sampleFamily_mem_VNP1LE2
#print axioms VNP1Char2.sampleFamily_mem_VNP1BIZ

-- Firewall theorems.
#print axioms VNP1Char2.kappa_tau_zero_fails
#print axioms VNP1Char2.kappa_tau_one_fails
#print axioms VNP1Char2.ternary_error_nonzero_without_exclusion
#print axioms VNP1Char2.shared_one_bit_auxiliary_changes_result
#print axioms VNP1Char2.unrestricted_label_supportTwo_firewall
#print axioms VNP1Char2.degree_three_flow_factor_support_three

end VNP1Char2
