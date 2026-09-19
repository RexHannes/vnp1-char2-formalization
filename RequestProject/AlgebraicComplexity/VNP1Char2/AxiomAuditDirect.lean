/-
# Axiom audit, direct formula-tree layer

`#print axioms` for every principal theorem added by the direct compiler.  The expected
(and observed) output is the standard Mathlib foundation `propext`, `Classical.choice`,
`Quot.sound`.  No project-specific axiom is declared anywhere in `VNP1Char2`, and the
direct layer uses no `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.DirectClassLevelTwo
import RequestProject.AlgebraicComplexity.VNP1Char2.RegressionTestsDirect
import RequestProject.AlgebraicComplexity.VNP1Char2.TwoPointWeights
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevelAudit

namespace VNP1Char2

/-! ## Non-vacuity -/

/-- The direct class theorem applies to a concrete family, so it is not vacuous. -/
theorem sampleFamily_mem_VNP1LE2_direct {F : Type} [Field F] [CharP F 2] {τ : F}
    (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) : VNP1LE2 (sampleFamily F) :=
  VPe_subset_VNP1LE2_direct hτ0 hτ1 sampleFamily_mem_VPe

/-! ## Axiom audit -/

-- The direct branch gadget.
#print axioms VNP1Char2.branch_identity
#print axioms VNP1Char2.branch_truth_table
#print axioms VNP1Char2.numVars_branchFactors_le
#print axioms VNP1Char2.prod_branchFactors
#print axioms VNP1Char2.sum_prod_branchFactors

-- Cube flattening used by the direct compiler.
#print axioms VNP1Char2.sum_cube_sum
#print axioms VNP1Char2.sum_cube_unit
#print axioms VNP1Char2.sum_prod_split
#print axioms VNP1Char2.one_add_boolVal_add_boolVal
#print axioms VNP1Char2.Formula.sum_pinned
#print axioms VNP1Char2.Formula.bodyProd_child

-- Counts, support and the activation semantics.
#print axioms VNP1Char2.Formula.card_taux
#print axioms VNP1Char2.Formula.leaves_eq_gates_succ
#print axioms VNP1Char2.Formula.length_bodyFactors
#print axioms VNP1Char2.Formula.numVars_bodyFactors_le
#print axioms VNP1Char2.Formula.condZ_var
#print axioms VNP1Char2.Formula.condZ_const
#print axioms VNP1Char2.Formula.condZ_mul
#print axioms VNP1Char2.Formula.condZ_add
#print axioms VNP1Char2.Formula.condZ_spec

-- The direct representation and the finite compiler theorem.
#print axioms VNP1Char2.Formula.directRep_value
#print axioms VNP1Char2.Formula.directRep_supportLE_two
#print axioms VNP1Char2.Formula.directRep_numAux
#print axioms VNP1Char2.Formula.directRep_numFactors
#print axioms VNP1Char2.Formula.directRep_numAux_le
#print axioms VNP1Char2.Formula.directRep_numAux_eq_two_size_sub
#print axioms VNP1Char2.Formula.directRep_two_numFactors_le
#print axioms VNP1Char2.Formula.directRep_numFactors_le
#print axioms VNP1Char2.Formula.has_supportTwo_representation_direct
#print axioms VNP1Char2.Formula.has_supportTwo_representation_direct_of_exists_tau

-- The direct class-level containment and its corollaries.
#print axioms VNP1Char2.nondetVPe_subset_VNP1LE2_direct
#print axioms VNP1Char2.VPe_subset_VNP1LE2_direct
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE2_direct
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE2_direct_of_exists_tau
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE2_direct_of_natCard
#print axioms VNP1Char2.nondetVPe_subset_VNP1BIZ_direct
#print axioms VNP1Char2.sampleFamily_mem_VNP1LE2_direct

-- Regression tests and firewalls.
#print axioms VNP1Char2.directRep_value_addMul
#print axioms VNP1Char2.directRep_counts_mixed
#print axioms VNP1Char2.directRep_fresh_dup
#print axioms VNP1Char2.branch_unrestricted_fails
#print axioms VNP1Char2.Formula.has_supportTwo_representation_direct_GF4
#print axioms VNP1Char2.Formula.has_supportTwo_representation_direct_GF8
#print axioms VNP1Char2.Formula.has_supportTwo_representation_direct_GF16

-- The optional two-point weight identity.
#print axioms VNP1Char2.two_point_identity
#print axioms VNP1Char2.muVal_tau_succ

/-! ## Independence firewall

A machine-checked check that the direct theorems really do not depend on the frozen
graph/path correctness theorems: the transitive constant dependencies of the direct finite
compiler theorem and of the direct class-level containment are collected and checked
against the list of forbidden graph/path results.  The check raises an elaboration error
(and so breaks the build) if any of them is used. -/

open Lean in
/-- All constants transitively used by a declaration. -/
private partial def transDeps (env : Environment) (seen : Std.HashSet Name) (n : Name) :
    Std.HashSet Name :=
  if seen.contains n then seen
  else
    let seen := seen.insert n
    match env.find? n with
    | none => seen
    | some ci =>
        let cs := ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
        cs.foldl (fun s m => transDeps env s m) seen

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let forbidden : List Name :=
    [`VNP1Char2.Formula.rep2_value,
     `VNP1Char2.Formula.has_supportTwo_affineHypercubeRepresentation,
     `VNP1Char2.Formula.has_supportTwo_representation_of_exists_tau,
     `VNP1Char2.PathGraph.graphRep2_value,
     `VNP1Char2.PathGraph.graphRep2_supportLE_two,
     `VNP1Char2.Formula.toDag_value,
     `VNP1Char2.nondetVPe_subset_VNP1LE2]
  for target in [`VNP1Char2.Formula.has_supportTwo_representation_direct,
                 `VNP1Char2.nondetVPe_subset_VNP1LE2_direct] do
    let deps := transDeps env {} target
    for f in forbidden do
      if deps.contains f then
        throwError "INDEPENDENCE FIREWALL VIOLATION: {target} depends on {f}"
  IO.println "independence firewall: the direct theorems use no graph/path correctness theorem"

end VNP1Char2
