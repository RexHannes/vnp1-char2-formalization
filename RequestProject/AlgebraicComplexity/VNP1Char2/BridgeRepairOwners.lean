/-
# Status after the final bridge repair (append-only)

`OpenOwners.lean`, `ClassLevelOwners.lean`, `SupportTwoOwners.lean` and
`DirectCompilerOwners.lean` are left untouched; this file records only the status of the
two certification-coverage items repaired in this layer.  Nothing here is an axiom, and no
banked proof was modified: both compilers (graph/path and direct formula-tree) are frozen.

## BANKED IN THIS LAYER (machine-checked)

* `STANDARD_P_FAMILY_DEGREE` — **closed**.  `VNP1Char2.IsPFamily` is the standard p-family
  predicate (polynomially many variables *and* polynomially bounded total degree).
  `VNP1Char2.Formula.totalDegree_eval_le` (`deg f ≤ size f`) gives
  `VNP1Char2.VPe.isPFamily`; `VNP1Char2.AffineHypercubeRep.totalDegree_value_le`
  (`deg ≤ M`, hypercube summation does not raise the degree) gives
  `VNP1Char2.VNP1.isPFamily`, hence `VNP1LE3.isPFamily` and `VNP1LE2.isPFamily`;
  `VNP1Char2.totalDegree_aeval_le` gives `VNP1Char2.NondetClosure.isPFamily` and
  `VNP1Char2.nondetVPe_isPFamily`.  The standard-universe forms of the class theorem are
  `VNP1Char2.nondetVPe_eq_VNP1LE2_standard`,
  `VNP1Char2.nondetVPe_subset_VNP1LE2_standard`,
  `VNP1Char2.VNP1LE2_subset_nondetVPe_standard` and
  `VNP1Char2.VPe_subset_VNP1LE2_standard`.

* `LITERAL_BIZ_W_PLUS_BRIDGE` — **closed**.  `VNP1Char2.VNP1BIZWPlus` requires of every
  factor *both* total degree at most one *and* variable support at most two.
  `VNP1Char2.VNP1LE2_subset_VNP1BIZWPlus` is the literal bridge, consuming the certified
  syntactic `SupportLE 2` property through
  `VNP1Char2.AffineForm.toPoly_vars_card_le`; `VNP1Char2.VNP1BIZWPlus.toVNP1BIZ` is the
  forgetful inclusion into the weaker degree-only class.
  `VNP1Char2.totalDegree_one_not_supportTwo` is the firewall showing the support condition
  is a genuine strengthening.

* `FIELD_SCOPE` — no change required.  The canonical positive hypothesis remains
  `∃ τ : F, τ ≠ 0 ∧ τ ≠ 1` (`VNP1Char2.field_scope_marker`); the finite-cardinality forms
  are corollaries only, and no statement uses type equality or inequality with `F₂`.

## UNCHANGED / STILL EXTERNAL

* Valiant's `VNP_e = VNP` and the Bringmann–Ikenmeyer–Zuiddam characteristic-not-two and
  `F₂` results remain external literature; they are neither formalized nor axiomatized.
* This layer adds no evaluator and therefore no P-vs-NP, VP-vs-VNP or runtime consequence,
  and no novelty claim.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.BridgeRepairAudit

namespace VNP1Char2

/-- Marker: the bridge-repair layer is a certification layer about the *classes*; it adds
no evaluator and no new compiler, and both banked compilers are untouched. -/
theorem bridge_repair_is_certification_only : True := trivial

end VNP1Char2
