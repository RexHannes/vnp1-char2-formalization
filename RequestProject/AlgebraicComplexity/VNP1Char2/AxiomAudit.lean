/-
# Axiom audit

`#print axioms` for every principal theorem of this layer.  The expected (and observed)
output is the standard Mathlib foundation `propext`, `Classical.choice`, `Quot.sound`.
No project-specific axiom is declared anywhere in `VNP1Char2`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.OpenOwners
import RequestProject.AlgebraicComplexity.VNP1Char2.RegressionTests
import RequestProject.AlgebraicComplexity.VNP1Char2.PathTheorem

namespace VNP1Char2

-- The four-factor identity and the legality of the denominator.
#print axioms VNP1Char2.fourFactor_identity_denominator_free
#print axioms VNP1Char2.delta_ne_zero
#print axioms VNP1Char2.fourFactor_identity
#print axioms VNP1Char2.fourFactorSum_mvPolynomial

-- The gadget expanding `1 + x*y` into four affine factors over two fresh Boolean bits.
#print axioms VNP1Char2.sum_prod_gadgetFactors

-- Flattening of nested Boolean hypercube sums.
#print axioms VNP1Char2.sum_sumCube

-- The path selector theorem.
#print axioms VNP1Char2.PathGraph.path_selector_iff

-- The graph-level compiler: value, support and size.
#print axioms VNP1Char2.PathGraph.graphRep_value
#print axioms VNP1Char2.PathGraph.graphRep_supportLE_three
#print axioms VNP1Char2.PathGraph.graphRep_numAux
#print axioms VNP1Char2.PathGraph.graphRep_numFactors

-- The formula-generated DAG.
#print axioms VNP1Char2.Formula.toDag_value
#print axioms VNP1Char2.Formula.toDag_goodDeg

-- The main compiler theorem and its field corollaries.
#print axioms VNP1Char2.Formula.rep_value
#print axioms VNP1Char2.Formula.has_supportThree_affineHypercubeRepresentation
#print axioms VNP1Char2.Formula.has_supportThree_representation_of_card_gt_two
#print axioms VNP1Char2.Formula.has_supportThree_representation_of_natCard_gt_two
#print axioms VNP1Char2.no_root_of_cyclotomic_three_GF8

-- Firewall theorems.
#print axioms VNP1Char2.tau_zero_fails
#print axioms VNP1Char2.tau_one_fails
#print axioms VNP1Char2.shared_auxiliary_changes_result
#print axioms VNP1Char2.unrestricted_label_support_firewall

end VNP1Char2
