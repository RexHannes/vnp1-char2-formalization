/-
# Open owners and scope firewall

This file contains **no** mathematical content beyond pointers; it records, in one place,
what is machine-checked in this layer and what is not.  Nothing here is an axiom.

## BANKED (machine-checked in this layer)

* `FOUR_FACTOR_IDENTITY` —
  `VNP1Char2.fourFactor_identity_denominator_free`, `VNP1Char2.fourFactor_identity`,
  `VNP1Char2.fourFactorSum_mvPolynomial`, `VNP1Char2.delta_ne_zero`.
  Formal polynomial identity; `X`, `Y` are never assumed Boolean.
* `PATH_SELECTOR` — `VNP1Char2.PathGraph.path_selector_iff`.
* `QUADRATIC → AFFINE GADGET EXPANSION` —
  `VNP1Char2.sum_prod_gadgetFactors`, `VNP1Char2.compiled_value`
  (every quadratic factor `1 + z_a z_b` and `1 + z_a(ℓ_a + 1)` is expanded through the
  four-factor gadget, with two fresh auxiliaries per occurrence).
* `FORMULA_COMPILER` — `VNP1Char2.Formula.rep_value`.
* `SUPPORT_THREE` — `VNP1Char2.PathGraph.graphRep_supportLE_three`,
  `VNP1Char2.Formula.rep_supportLE_three` (formula-generated graphs only).
* `SIZE_ACCOUNTING` — `VNP1Char2.PathGraph.graphRep_numAux`,
  `VNP1Char2.PathGraph.graphRep_numFactors`, `VNP1Char2.Formula.rep_numAux_le`,
  `VNP1Char2.Formula.rep_numFactors_le`.
* `FINITE_HYPERCUBE_REPRESENTATION` —
  `VNP1Char2.Formula.has_supportThree_affineHypercubeRepresentation`.
* `FIELD_SCOPE` — `VNP1Char2.exists_tau_of_two_lt_card`,
  `VNP1Char2.exists_tau_of_two_lt_natCard`,
  `VNP1Char2.Formula.has_supportThree_representation_of_card_gt_two`,
  `VNP1Char2.Formula.has_supportThree_representation_of_natCard_gt_two`,
  and the `GF(8)` firewall `VNP1Char2.no_root_of_cyclotomic_three_GF8`
  (no `F₄` subfield is used anywhere).

## OPEN (not formalized here, and not assumed anywhere here)

* `SUPPORT_TWO_UPGRADE` — a support-two version of the compiler.
* `CLASS_LEVEL_VP_e_TO_VNP1` — the p-family/class-level statement
  `VP_e(F) ⊆ VNP₁^{[≤3]}(F)`.  The machine-checked compiler is the per-formula content of
  this inclusion with explicit linear bounds `q ≤ 44·size`, `M ≤ 84·size`; turning it into
  a class statement needs a p-family library, which is not developed here.
* `FULL_VNP1_CLASSIFICATION` — `VNP₁(F) = VNP(F) ↔ F ≇ F₂`.  The characteristic ≠ 2 case
  and the `F₂` separation are external literature results and are *not* imported as
  axioms.
* `NOVELTY` — not a mathematical statement and deliberately not a Lean theorem.

## SCOPE-DEAD (must not be inferred from this layer)

The theorem proved here is a **representation** theorem: it exhibits a hypercube sum of a
product of affine factors, it does *not* supply any evaluator of that sum.  Nothing here
implies, or is intended to support, any of:

* `P = NP` or `P ≠ NP`;
* `VP = VNP`;
* a deterministic CircuitSAT algorithm;
* a sub-`2^k` evaluation of a `k`-variable hypercube sum;
* any runtime consequence whatsoever.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.FieldCorollary

namespace VNP1Char2

/-- Marker: this layer proves a representation theorem only.  Reading the statement of
`Formula.has_supportThree_affineHypercubeRepresentation` makes the scope explicit: it is an
existence statement about a finite list of affine factors and a finite set of Boolean
auxiliaries, with no computational claim attached. -/
theorem scope_is_representation_only {ι F : Type} [Field F] [CharP F 2] (f : Formula ι F)
    {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    ∃ R : AffineHypercubeRep ι F, R.value = f.eval :=
  ⟨f.rep τ, f.rep_value hτ0 hτ1⟩

end VNP1Char2
