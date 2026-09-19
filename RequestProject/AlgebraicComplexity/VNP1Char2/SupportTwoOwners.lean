/-
# Status of the support-two layer (append-only update of `OpenOwners`)

`OpenOwners.lean` and `ClassLevelOwners.lean` are left untouched; this file records the
status of the items they listed as open, after the support-two layer.  Nothing here is an
axiom.

## BANKED (machine-checked, `[Field F]`, `[CharP F 2]`, `τ ≠ 0`, `τ ≠ 1`)

* `TERNARY_IDENTITY` — `VNP1Char2.ternFactor_identity` (and the denominator-free
  `ternFactor_identity_denominator_free`), a formal polynomial identity with the cubic
  error kept explicit.
* `SUPPORT_TWO_GADGET` — `VNP1Char2.twoFactor_identity`: `1 + x y` as one summed Boolean
  bit and three affine factors; `VNP1Char2.kappa_ne_zero` for the denominator.
* `SUPPORT_TWO_PATH_COMPILER` — `VNP1Char2.PathGraph.graphRep2_value`,
  `graphRep2_supportLE_two`, `graphRep2_numAux`, `graphRep2_numFactors`.
* `SUPPORT_TWO_FINITE_COMPILER` — **closed**:
  `VNP1Char2.Formula.has_supportTwo_affineHypercubeRepresentation`, with `q ≤ 26·size f`
  and `M ≤ 70·size f`.
* `CLASS_LEVEL_SUPPORT_TWO` — **closed**: `VNP1Char2.nondetVPe_eq_VNP1LE2`
  (`N(VP_e(F)) = VNP₁^{[≤2]}(F)`), with the field forms `..._of_exists_tau` and
  `..._of_natCard`.
* `WIDTH_ONE_ABP_BRIDGE` — `VNP1Char2.VNP1LE2_subset_VNP1BIZ`: every support-two
  affine-product hypercube family is a hypercube sum of a product of polynomials of total
  degree at most one, i.e. of width-one-ABP edge labels.

## PARTIAL / OPEN

* `SHARP_CONSTANTS` — PARTIAL.  The memo's first graph identity is **proved**:
  `VNP1Char2.Formula.toDag_numPairs : P = 4a`, whence
  `VNP1Char2.Formula.rep2_numAux_le_sharp : q ≤ 14·size f` (the memo's constant) and
  `VNP1Char2.Formula.rep2_numFactors_le_sharp : M ≤ 34·size f` (the memo conjectured
  `32 s`).  The coarse bounds `q ≤ 26 s`, `M ≤ 70 s` remain available in
  `MainCompilerTwo.lean`.  The second conjectured identity `D + B = 2a` is **not** proved:
  the number of degree-three vertices of a formula graph is not a function of `(l, a, u)`
  alone.  Nothing downstream depends on the constants, only on `O(s)`.
* `GADGET_MINIMALITY` — the statement that `(q, m) = (1, 3)` is locally optimal; see
  `GadgetMinimality.lean` for what is machine-checked and what is not.

## NOT FORMALIZED (and not assumed anywhere)

* `STANDARD VNP IDENTIFICATION` — the literature classes `VNP`, `VNP₁` and Valiant's
  theorem `VNP_e = VNP` are not formalized.  `VNP1BIZ` is an internal definition that
  matches the literature *shape* (width-one ABP body), but no theorem here identifies any
  internal class with a literature class.
* `FULL_VNP1_CLASSIFICATION` — `VNP₁(F) = VNP(F) ↔ F ≇ F₂` remains an external literature
  consequence.
* `NOVELTY` — not a mathematical statement and deliberately not a Lean theorem.

## SCOPE-DEAD

The support-two layer is a *representation* statement about hypercube sums; it supplies no
evaluator.  It implies nothing about `P` versus `NP`, about `VP` versus `VNP`, and no
runtime consequence of any kind.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.AxiomAuditTwo

namespace VNP1Char2

/-- Marker: the support-two class statement is an inclusion between representation classes,
with no computational content attached.  Membership in `VNP1LE2` asserts only the
existence, for each `n`, of a finite list of affine factors and a finite Boolean cube. -/
theorem supportTwo_scope_is_representation_only {F : Type} [Field F] [CharP F 2] {τ : F}
    (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) {f : PolyFamily F} (hf : NondetClosure VPe f) :
    ∃ R : ∀ n, AffineHypercubeRep (Fin (f.nvars n)) F, ∀ n, (R n).value = f.poly n := by
  obtain ⟨hv, R, q, M, hq, hM, h⟩ := nondetVPe_subset_VNP1LE2 hτ0 hτ1 hf
  exact ⟨R, fun n => (h n).1⟩

end VNP1Char2
