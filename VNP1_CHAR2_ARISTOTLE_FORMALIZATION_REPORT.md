# VNP₁ characteristic-two formalization — checkpoint recovery report

All statements below refer to the Lean layer
`RequestProject/AlgebraicComplexity/VNP1Char2/` and its aggregator
`RequestProject/AlgebraicComplexity/VNP1Char2.lean`.

## 0. Requested status block

```text
CHECKPOINT RECOVERY:
PASS

FormulaDegrees:
PASS

MainCompiler:
PASS

PathTheorem:
PASS

FieldCorollary:
PASS  (repaired: the `GaloisField` regression statements needed `Nat.card` instead of
       `Fintype.card`, since Mathlib supplies only a `Finite` instance for `GaloisField p n`)

MAIN SUPPORT-THREE THEOREM:
BANKED

FIELD SCOPE:
`[Field F] [CharP F 2]` together with an explicit element `τ : F`, `τ ≠ 0`, `τ ≠ 1`
(so infinite characteristic-two fields are covered).  For finite fields the element is
produced from `2 < Fintype.card F` (equivalently `2 < Nat.card F`).  No `F₄` subfield and
no root of `x² + x + 1` is used anywhere.

PATH SELECTOR:
BANKED
```

## A. Executive verdict

```text
FOUR-FACTOR IDENTITY:            PROVED
FORMAL-POLYNOMIAL STATUS:        PROVED (identity in MvPolynomial; X, Y never Boolean)
PATH SELECTOR:                   PROVED
QUADRATIC→AFFINE GADGET EXPANSION: PROVED
EDGE-WEIGHT COMPILER:            PROVED
SIZE ACCOUNTING:                 PROVED
SUPPORT ≤ 3:                     PROVED (formula-generated graphs only)
FINITE FORMULA → AFFINE-HYPERCUBE COMPILER: PROVED
CLASS-LEVEL CONSEQUENCE:         EXTERNAL-COROLLARY-ONLY (not formalized, not axiomatized)
NEW P-vs-NP RUNTIME CONSEQUENCE: NONE
```

## B. Principal theorems

| name | file | content |
|---|---|---|
| `VNP1Char2.fourFactor_identity_denominator_free` | `FourFactorIdentity.lean` | (ID′) `∑_{b,e} (x+L)(x+τL+c)(τ⁴y+M)(τ⁴y+τM+c) = Δ(1+xy)` in any ring with `2 = 0` |
| `VNP1Char2.delta_ne_zero` | `FourFactorIdentity.lean` | `τ ≠ 0, τ ≠ 1 ⟹ Δ = τ⁴(τ+1)² ≠ 0` |
| `VNP1Char2.fourFactor_identity` | `FourFactorIdentity.lean` | (ID) `∑_{b,e} J_τ(x,y;b,e) = 1 + xy` |
| `VNP1Char2.fourFactorSum_mvPolynomial` | `FourFactorIdentity.lean` | (ID) for the formal indeterminates `X 0`, `X 1` |
| `VNP1Char2.sum_prod_gadgetFactors` | `OnePlusProductGadget.lean` | the four affine factors of the gadget, summed over two fresh bits, equal `1 + x·y` |
| `VNP1Char2.sum_sumCube` | `HypercubeFlattening.lean` | flattening of nested Boolean cubes (`A ⊕ K × Bool`) |
| `VNP1Char2.PathGraph.path_selector_iff` | `PathTheorem.lean` | (PATH) `selectorVal = 1 ↔ the selection is the edge set of a directed `s → t` walk` |
| `VNP1Char2.compiled_value` | `Compiler.lean` | (ABP) the compiled affine-product hypercube sum equals the graph polynomial |
| `VNP1Char2.PathGraph.graphRep_value` | `GraphCompiler.lean` | same, for a labelled DAG |
| `VNP1Char2.PathGraph.graphRep_supportLE_three` | `SupportThree.lean` | (SUPPORT3) under total degree ≤ 3 and single-variable labels |
| `VNP1Char2.PathGraph.graphRep_numAux` / `graphRep_numFactors` | `CompilerSize.lean` | `q = 3|E| + 2P`, `M = |V| + 4(|E| + P)` |
| `VNP1Char2.Formula.toDag_value`, `toDag_goodDeg`, `toDag_card_V`, `toDag_card_E` | `FormulaDegrees.lean` | the formula DAG computes the formula, has total degree ≤ 3, and has `|V| = 2l + 2a`, `|E| = l + 4a + u` |
| `VNP1Char2.Formula.rep_value`, `rep_supportLE_three`, `rep_numAux_le`, `rep_numFactors_le` | `MainCompiler.lean` | value, support and linear size bounds of the compiled representation |
| `VNP1Char2.Formula.has_supportThree_affineHypercubeRepresentation` | `MainCompiler.lean` | **main theorem**: `q ≤ 44·size f`, `M ≤ 84·size f`, support ≤ 3 |
| `VNP1Char2.exists_tau_of_two_lt_card`, `exists_tau_of_two_lt_natCard` | `FieldCorollary.lean` | a field with more than two elements contains `τ ∉ {0,1}` |
| `VNP1Char2.Formula.has_supportThree_representation_of_card_gt_two` (and the `Nat.card` and `GF(8)` variants) | `FieldCorollary.lean` | finite characteristic-two fields with `> 2` elements |
| `VNP1Char2.no_root_of_cyclotomic_three_GF8` | `FieldCorollary.lean` | `x² + x + 1` has no root in `GF(8)` — no `F₄` subfield is needed |

## C. Repairs made in this continuation

1. `FieldCorollary.lean` did not compile: Mathlib provides `Finite (GaloisField p n)` but no
   `Fintype` instance, and `GaloisField.card` is stated with `Nat.card`.  The `GF(4)`,
   `GF(8)`, `GF(16)` regression statements were restated with `Nat.card`, and a `Nat.card`
   form of the general corollary (`exists_tau_of_two_lt_natCard`,
   `Formula.has_supportThree_representation_of_natCard_gt_two`) was added, together with the
   direct `GF(8)` instance `Formula.has_supportThree_representation_GF8`.  The
   `Fintype.card` version of the general corollary is unchanged.
2. The aggregator `VNP1Char2.lean` now imports every module of the layer, including
   `GraphCompiler`, `CompilerSize`, `SupportThree`, `FormulaToDAG`, `FormulaDegrees`,
   `MainCompiler`, `PathTheorem`, `FieldCorollary`, `RegressionTests`, `OpenOwners`,
   `AxiomAudit`.
3. `RequestProject/Main.lean` imports the aggregator with a single line.
4. New `RegressionTests.lean` (firewalls), `OpenOwners.lean` (scope statement),
   `AxiomAudit.lean` (`#print axioms`).

Repairs carried over from the earlier phase and re-verified here:
quadratic edge selectors `1 + z_a(ℓ_a+1)` and quadratic pair exclusions `1 + z_a z_b` are
both expanded through the four-factor gadget with **two fresh auxiliaries per occurrence**
(`GraphCompiler.gadgetX`/`gadgetY`, `Compiler.compiled`); pair exclusions are imposed at
*every* vertex including the source and the sink (`PathGraph.inPairs`, `outPairs`);
support ≤ 3 is claimed only for formula-generated bounded-degree graphs.

## D. Firewall / counterexample tests (`RegressionTests.lean`)

* `tau_zero_fails`, `tau_one_fails` — the excluded values `τ = 0`, `τ = 1` make `Δ = 0` and
  the four-factor sum collapses to `0 ≠ 1 + x·y`.  (Over `F₂` these are the only elements,
  which is exactly why the construction does not apply there.)
* `shared_auxiliary_changes_result` — `(∑_b A b)(∑_b B b) ≠ ∑_b A b·B b`: gadget auxiliaries
  must be fresh.
* `sum_bool_const_eq_zero` — an unused summed Boolean variable annihilates the sum in
  characteristic two, so none may be introduced.
* `unrestricted_label_support_firewall` — an edge labelled `x₁ + x₂ + x₃` yields a gadget
  factor of support `5 > 3`: `SUPPORT3` is **not** a theorem about arbitrary ABPs.

## E. Build result

```text
lake build RequestProject.AlgebraicComplexity.VNP1Char2.FormulaDegrees   → success
lake build RequestProject.AlgebraicComplexity.VNP1Char2.MainCompiler     → success
lake build RequestProject.AlgebraicComplexity.VNP1Char2.PathTheorem      → success
lake build RequestProject.AlgebraicComplexity.VNP1Char2.FieldCorollary   → success (after repair)
lake build                                                               → Build completed successfully
```
Only linter warnings (unused simp arguments, unused section variables) are emitted; no errors.

## F. Placeholder audit

A search of the whole `RequestProject` tree for
`sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `@[implemented_by]`
returns **two matches, both inside documentation comments** (in `OpenOwners.lean` and
`AxiomAudit.lean`, in the sentences stating that no axiom is declared).  There is no such
declaration anywhere in the layer.

## G. Axiom audit

`AxiomAudit.lean` runs `#print axioms` on all principal theorems.  Every one reports a
subset of

```text
[propext, Classical.choice, Quot.sound]
```

(`fourFactor_identity_denominator_free` reports `[propext, Quot.sound]`).  No
project-specific axiom is used.

## H. Machine-checked here vs imported literature

```text
MACHINE-CHECKED HERE
  four-factor identity (ID), (ID′), Δ ≠ 0
  path-selector theorem (PATH)
  quadratic → affine gadget expansion with fresh auxiliaries
  formula → bounded-degree labelled DAG, value preserved, acyclicity
  edge-weight compiler (ABP)
  size accounting q = 3|E| + 2P, M = |V| + 4(|E|+P), and the linear formula bounds
  support ≤ 3 for formula-generated graphs
  finite compiler theorem with q ≤ 44·s, M ≤ 84·s
  finite-field corollary for char 2 with more than two elements; GF(8) has no F₄ subfield

IMPORTED LITERATURE CONSEQUENCE (not formalized, not axiomatized)
  the characteristic ≠ 2 nondeterministic-width-one characterization
  the F₂ separation
  the classification VNP₁(F) = VNP(F) ⟺ F ≇ F₂
```

## I. Scope firewall

The banked theorem is a **representation** theorem.  It produces `O(s)` summed Boolean
variables and `O(s)` affine factors; it supplies **no** evaluator of the resulting
hypercube sum.  It therefore implies none of: `P = NP`, `P ≠ NP`, `VP = VNP`, a
deterministic CircuitSAT algorithm, a sub-`2^k` hypercube evaluator, or any runtime claim.
No novelty claim is made.

## J. Strict final verdict

```text
VNP1 CHARACTERISTIC-TWO FORMALIZATION

FOUR-FACTOR IDENTITY:              PROVED
FORMAL-POLYNOMIAL STATUS:          PROVED
PATH COMPILER:                     PROVED
QUADRATIC→AFFINE GADGET EXPANSION: PROVED
SIZE ACCOUNTING:                   PROVED
SUPPORT ≤ 3:                       PROVED (formula-generated graphs)
FINITE COMPILER THEOREM:           PROVED
FIELD SCOPE:                       [Field F] [CharP F 2] and τ ≠ 0, τ ≠ 1;
                                   finite case from 2 < Fintype.card F / 2 < Nat.card F
CLASS-LEVEL VNP₁ CONSEQUENCE:      EXTERNAL COROLLARY / OPEN
P-vs-NP CONSEQUENCE:               NONE
FIRST REMAINING MATHEMATICAL OWNER: support-two upgrade (not attempted); class-level
                                   VP_e ⊆ VNP₁^{[≤3]} p-family layer
LAKE BUILD:                        PASS
PLACEHOLDER AUDIT:                 PASS
AXIOM AUDIT:                       propext, Classical.choice, Quot.sound only
OVERALL:                           FORMALLY BANKABLE (as a finite representation theorem)
```
