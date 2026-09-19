/-
# Status of the direct formula-tree layer (append-only status entry)

`OpenOwners.lean`, `ClassLevelOwners.lean` and `SupportTwoOwners.lean` are left untouched.
This file records the status of the *direct* (formula-tree activation) branch added on top
of them.  Nothing here is an axiom, and no statement of the frozen graph/path layer is
modified, weakened or reproved.

## BANKED HERE (machine-checked; `[Field F]`, `[CharP F 2]`, `τ ≠ 0`, `τ ≠ 1`)

* `DIRECT_BRANCH_GADGET` — `VNP1Char2.branch_identity` and
  `VNP1Char2.branch_truth_table`: for Boolean `a, b, c`,
  `∑_{h ∈ {0,1}} Γ_τ(a,b,c;h) = (1+a+b+c)(1+ab)`, with support exactly
  `{(0,0,0), (1,0,1), (0,1,1)}`; one fresh auxiliary bit, six affine factors.
  `VNP1Char2.numVars_branchFactors_le`: every factor has support at most two.
* `DIRECT_ACTIVATION_SEMANTICS` — `VNP1Char2.Formula.condZ_spec`:
  `Z_f(0) = 1` and `Z_f(1) = f.eval`, by structural induction on the formula, with
  `condZ_var`, `condZ_const`, `condZ_mul` and `condZ_add` as the four node rules.
* `DIRECT_FRESHNESS_AND_FLATTENING` — `VNP1Char2.sum_cube_sum`,
  `VNP1Char2.sum_cube_unit`, `VNP1Char2.sum_prod_split`,
  `VNP1Char2.Formula.sum_pinned`, `VNP1Char2.Formula.bodyProd_child`.  Every cube split is
  along a disjoint sum of index types; the false step
  `(∑_b A_b)(∑_c B_c) = ∑_b A_b B_b` is never used.
* `DIRECT_FINITE_COMPILER` — **closed**:
  `VNP1Char2.Formula.has_supportTwo_representation_direct`, with `SupportLE 2`,
  `q ≤ 2·size f`, `2M ≤ 9·size f` and `M ≤ 5·size f`; exact counts
  `q = 2l + 2a + u` (`directRep_numAux`) and `M = 1 + 3l + 6a + 2u`
  (`directRep_numFactors`).
* `DIRECT_CLASS_FORWARD` — **closed**:
  `VNP1Char2.nondetVPe_subset_VNP1LE2_direct` : `N(VP_e(F)) ⊆ VNP₁^{[≤2]}(F)`, proved
  from the direct compiler alone.
* `TWO_POINT_WEIGHTS` — `VNP1Char2.two_point_identity` (optional; explains the
  `|F| > 2` threshold).

## REUSED FROZEN THEOREMS (not reproved here)

* the graph/path support-two compiler
  (`VNP1Char2.Formula.has_supportTwo_affineHypercubeRepresentation`) — independent
  cross-check only; it is **not** used by any direct theorem;
* the reverse containment `VNP1Char2.VNP1LE2_subset_nondetVPe` and the
  literature-shaped bridge `VNP1Char2.VNP1LE2_subset_VNP1BIZ`, used only *after* the new
  forward containment, to package `nondetVPe_eq_VNP1LE2_direct` and
  `nondetVPe_subset_VNP1BIZ_direct`.

## SCOPE FIREWALLS

* `VNP1Char2.branch_unrestricted_fails`: the branch identity is **false** without the
  Boolean restriction on the parent value, so `(BRANCH)` is asserted only for Boolean
  arguments.
* The layer is a *representation* theorem.  It supplies no evaluator of the hypercube sum,
  and therefore yields no `P = NP`, `P ≠ NP`, `VP = VNP`, `VP ≠ VNP` or runtime
  consequence.
* No literature theorem (Valiant's `VNP_e = VNP`; Bringmann–Ikenmeyer–Zuiddam's
  characteristic-not-two theorem or their `F₂` separation) is formalized or axiomatized.
* No novelty claim is made; `NOVELTY` is not a Lean statement.

## OPEN / NOT ATTEMPTED

* Minimality of the six-factor branch gadget (five- or four-factor universal branch
  gadgets) — not attempted.
* Any identification of the internal classes with the literature classes `VNP₁`, `VNP` —
  open, and deliberately not axiomatized.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.AxiomAuditDirect

namespace VNP1Char2

/-- A marker recording that the direct layer is a representation statement: it asserts the
existence of an affine-product Boolean-hypercube representation, not an evaluation
procedure for it. -/
theorem direct_layer_is_representation_only {ι F : Type} [Field F] [CharP F 2]
    (f : Formula ι F) {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    ∃ R : AffineHypercubeRep ι F, R.Represents f.eval ∧ R.SupportLE 2 :=
  let ⟨R, hR, hS, _, _, _⟩ := f.has_supportTwo_representation_direct hτ0 hτ1
  ⟨R, hR, hS⟩

end VNP1Char2
