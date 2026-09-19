# VNP₁ over characteristic-two fields — SUPPORT-TWO formalization report

This report covers the **support-two** layer only.  The earlier support-three layer is
frozen: no file of it was modified, renamed, weakened or reproved, and the only edit to an
existing file is ten appended `import` lines in the aggregator
`RequestProject/AlgebraicComplexity/VNP1Char2.lean`.  The earlier reports
(`VNP1_CHAR2_ARISTOTLE_FORMALIZATION_REPORT.md`,
`VNP1_CHAR2_CLASS_LEVEL_REPORT.md`) remain valid as written.

---

## A. Executive verdict

```text
TERNARY IDENTITY (formal polynomial identity):        PROVED
SUPPORT-TWO 1+xy GADGET (1 bit, 3 factors):           PROVED
κ ≠ 0 DENOMINATOR LEGALITY:                           PROVED
POINTWISE CUBIC-ERROR KILLING (proof-order firewall): PROVED
SUPPORT-TWO PATH/DAG COMPILER:                        PROVED
SUPPORT ≤ 2 (formula-generated graphs):               PROVED
FINITE FORMULA → SUPPORT-TWO HYPERCUBE COMPILER:      PROVED   (q ≤ 26 s, M ≤ 70 s)
CLASS-LEVEL N(VP_e) = VNP₁^{[≤2]}:                    PROVED   (internal classes)
WIDTH-ONE-ABP LITERATURE BRIDGE VNP₁^{[≤2]} ⊆ VNP₁,BIZ: PROVED (internal definition)
SHARP CONSTANTS P = 4a, q ≤ 14s, M ≤ 34s:             PROVED
SHARP CONSTANT D + B = 2a (and M ≤ 32s):              NOT PROVED (see §D)
GADGET MINIMALITY (q_min, m_min) = (1,3):              PARTIAL  (see §E)
NEW P-vs-NP / VP-vs-VNP RUNTIME CONSEQUENCE:           NONE
```

Field scope of every positive theorem: `[Field F]`, `[CharP F 2]`, together with an
explicit `τ : F` with `τ ≠ 0` and `τ ≠ 1` (equivalently, for finite fields,
`2 < Nat.card F`).  Infinite characteristic-two fields are covered.  No subfield `F₄`, and
no root of `x² + x + 1`, is ever required.

---

## B. The mathematics, in the required proof order

Write `κ = τ(τ+1)`.

1. **Ternary identity** (`ternFactor_identity_denominator_free`, `ternFactor_identity`):
   for arbitrary ring elements `a, b, c` of a commutative ring of characteristic two, and
   with only `h` Boolean,

   ```text
   ∑_{h∈{0,1}} (τ+1+h)(a+τ+h)(b+τ+h)(c+τ+h) = κ(1 + a + b + c) + abc.
   ```

   This is a genuine polynomial identity; the cubic error `abc` is kept explicit.

2. **The error is not formally removable** (`cubic_error_not_formally_zero`):
   `X₀X₁X₂(1 + X₀X₁) ≠ 0` in `MvPolynomial (Fin 3) F`.  Consequently the compiler never
   rewrites `abc(1+ab) = 0` inside an unrestricted polynomial ring.

3. **Boolean selector assignment fixed first.**  The generic compiler theorem
   `compiled2_value` takes the hypothesis

   ```text
   hkill : ∀ (z : A → Bool) (j : T), error(j, z) * ∏_k (1 + x_k(z) y_k(z)) = 0,
   ```

   i.e. the error is discharged *pointwise, for each fixed Boolean selection `z`*, and only
   afterwards is the Boolean hypercube summed.

4. **Same-head/same-tail exclusion supplies the killer.**  At an internal vertex of total
   degree three the three incident edges are distributed over the two sides, so two of them
   share a head or share a tail (`exists_ternTriple`); the corresponding pair-exclusion
   factor `1 + z_a z_b` occurs in the product, and
   `boolVal_mul_mul_one_add_mul : u v w (1 + u v) = 0` finishes it
   (`PathGraph.tern_error_kill`).

5. **Summation over the hypercube and the final `MvPolynomial` identity.**
   `PathGraph.graphRep2_value` and `Formula.rep2_value` state equalities of polynomials in
   the *original* formula variables; only the selector bits and the gadget auxiliaries are
   ever specialised to Boolean values.

6. **Freshness.**  The auxiliary index type of the compiled representation is
   `A ⊕ (T ⊕ K)`: the selection bits, one fresh bit per ternary occurrence, one fresh bit
   per quadratic occurrence.  Distinct occurrences therefore have disjoint auxiliaries by
   construction, and the exchange of products and sums is justified by
   `prod_sum_flatten_one`, `sum_cube_pair_flatten` and `sum_cube3` — never by the false
   step `(∑_b A_b)(∑_c B_c) = ∑_b A_b B_b`, which is refuted in
   `shared_one_bit_auxiliary_changes_result`.  No summed Boolean variable occurring in no
   factor is introduced (in characteristic two such a variable would annihilate the value).

---

## C. Exact theorem list

All statements are in namespace `VNP1Char2`; `F` is a field with `CharP F 2` and
`τ ≠ 0`, `τ ≠ 1` wherever `τ` occurs.

### `VNP1Char2/TernaryIdentity.lean`

| name | statement |
| --- | --- |
| `kappaVal`, `twoFactorBody`, `ternFactorBody` | definitions of `κ = τ(τ+1)` and the two gadget bodies |
| `twoFactor_identity_denominator_free` | `∑_h (τ+1+h)(x+τ+h)(κy+τ+h) = κ(1+xy)` in any ring with `2 = 0` |
| `ternFactor_identity_denominator_free` | `∑_h (τ+1+h)(a+τ+h)(b+τ+h)(c+τ+h) = κ(1+a+b+c) + abc` |
| `boolVal_mul_mul_one_add_mul` | `u v w (1 + u v) = 0` for Boolean `u, v, w` (pointwise) |
| `kappa_ne_zero` | `τ ≠ 0 → τ ≠ 1 → κ ≠ 0` |
| `kappa_eq_zero_of_eq_zero`, `kappa_eq_zero_of_eq_one` | the excluded values really are excluded |
| `twoFactor_identity` | `∑_h κ⁻¹(τ+1+h)(x+τ+h)(κy+τ+h) = 1 + xy` |
| `ternFactor_identity` | `∑_h κ⁻¹(…) = (1+a+b+c) + κ⁻¹abc` |
| `twoFactorSum_mvPolynomial`, `ternFactorSum_mvPolynomial` | the two identities in `MvPolynomial (Fin 2) F`, `MvPolynomial (Fin 3) F` |
| `cubic_error_not_formally_zero` | `X₀X₁X₂(1+X₀X₁) ≠ 0` |

### `VNP1Char2/SupportTwoGadget.lean`

| name | statement |
| --- | --- |
| `gadget2Factors` | the three affine forms of the `1+xy` gadget, one fresh auxiliary |
| `numVars_gadget2Factors_le` | each factor has `numVars ≤ max(x,y) + 1` |
| `sum_prod_gadget2Factors` | their Boolean sum is `1 + x·y` |
| `ternFactors` | the four affine forms of the ternary gadget, one fresh auxiliary |
| `numVars_ternFactors_le` | each ternary factor has `numVars ≤ 2` |
| `sum_prod_ternFactors` | their Boolean sum is `(1+a+b+c) + κ⁻¹abc` |

### `VNP1Char2/CompilerTwo.lean`

| name | statement |
| --- | --- |
| `prod_sum_flatten_one`, `sum_cube_pair_flatten`, `cube3Equiv`, `sum_cube3` | hypercube flattening for one-bit gadgets and for the triple disjoint union |
| `prod_add_err_mul` | if every `e j` annihilates `W` then `(∏(p j + e j))·W = (∏ p j)·W` |
| `compiled2` | the compiled representation, auxiliaries `A ⊕ (T ⊕ K)` |
| `compiled2.numAux_eq` | `q = |A| + |T| + |K|` |
| `compiled2.numFactors_eq` | `M = #flowForms + 4|T| + 3|K|` |
| `compiled2.supportLE_two` | support ≤ 2 under `numVars ≤ 2` flow factors and `numVars ≤ 1` gadget inputs |
| `compiled2_value_raw` | unconditional value, cubic errors visible |
| `compiled2_value` | value with the errors removed, under the pointwise `hkill` |

### `VNP1Char2/GraphCompilerTwo.lean`

| name | statement |
| --- | --- |
| `TernTriple`, `exists_ternTriple` | the three incident edges at a degree-three vertex, two of them same-side |
| `ternVerts`, `TernIdx`, `ternTripleOf`, `ternA/B/C` | the ternary occurrences of a graph |
| `flowForms2` | the flow factors kept affine (constant `1` at ternary vertices) |
| `graphRep2` | the support-two compiled representation of a labelled DAG |
| `tern_eq_flowFactor`, `prod_flowForms2`, `prod_ternIdx`, `prod_flow_all` | the flow part is reproduced exactly |
| `tern_error_kill` | the pointwise cubic-error killer at a ternary vertex |
| `graphRep2_value` | `(graphRep2 G lab τ).value = val G ℓ` |
| `flowForms2_numVars_le_two`, `graphRep2_supportLE_two` | **(SUPPORT2)** |
| `graphRep2_numAux`, `graphRep2_numFactors` | `q = 2|E| + D + P`, `M = |V| + 4D + 3(|E|+P)` |

### `VNP1Char2/MainCompilerTwo.lean`

| name | statement |
| --- | --- |
| `Formula.rep2`, `Formula.rep2_value` | the compiled representation of a formula computes it |
| `Formula.rep2_supportLE_two` | every affine factor has support ≤ 2 |
| `Formula.rep2_numAux_le` | `q ≤ 26 · size f` |
| `Formula.rep2_numFactors_le` | `M ≤ 70 · size f` |
| `Formula.has_supportTwo_affineHypercubeRepresentation` | **the main finite support-two compiler theorem** |
| `Formula.has_supportTwo_representation_of_exists_tau` | same, under `∃ τ, τ ≠ 0 ∧ τ ≠ 1` |

### `VNP1Char2/SharpConstants.lean`

| name | statement |
| --- | --- |
| `PathGraph.pairsAt`, `PathGraph.numPairs_eq_sum_pairsAt` | the pair count as a sum of vertex-local counts |
| `LabelledDag.leafDag_numPairs`, `mulDag_numPairs`, `addDag_numPairs` | `0`, `P+Q`, `P+Q+4` |
| `Formula.toDag_numPairs` | **`P = 4a`** |
| `Formula.rep2_numAux_le_sharp` | `q ≤ 14 · size f` |
| `Formula.rep2_numFactors_le_sharp` | `M ≤ 34 · size f` |
| `Formula.has_supportTwo_representation_sharp` | the main theorem with the sharp constants |

### `VNP1Char2/ClassLevelTwo.lean`

| name | statement |
| --- | --- |
| `VNP1LE2` | the internal support-two hypercube class |
| `VNP1LE2.toVNP1LE3` | support ≤ 2 implies support ≤ 3 |
| `nondetVPe_subset_VNP1LE2` | `N(VP_e(F)) ⊆ VNP₁^{[≤2]}(F)` (load-bearing) |
| `VPe_subset_VNP1LE2` | `VP_e(F) ⊆ VNP₁^{[≤2]}(F)` |
| `VNP1LE2_subset_nondetVPe` | reverse containment (through the frozen support-three theorem) |
| `nondetVPe_eq_VNP1LE2` (+ `_of_exists_tau`, `_of_natCard`) | **`N(VP_e(F)) = VNP₁^{[≤2]}(F)`** |
| `AffineForm.toPoly_totalDegree_le_one` | an affine form is a legal width-one-ABP edge label |
| `VNP1BIZ` | the literature-shaped class: hypercube sum of a product of total-degree-≤1 polynomials |
| `VNP1LE2_subset_VNP1BIZ`, `nondetVPe_subset_VNP1BIZ` | the minimal width-one-ABP bridge |

### `VNP1Char2/GadgetMinimality.lean`, `RegressionTestsTwo.lean`, `AxiomAuditTwo.lean`, `SupportTwoOwners.lean`

See §E and §F.

---

## D. Size accounting

For the formula-generated DAG with `l` leaves, `a` addition gates, `u` multiplication
gates and `s = l + a + u`:

```text
|E| = l + 4a + u ≤ 4s,      |V| = 2l + 2a ≤ 2s,
P   = |inPairs| + |outPairs| ≤ 4|E| ≤ 16s,
D   = #{internal vertices of total degree 3} ≤ |V| ≤ 2s.

q = 2|E| + D + P            ≤ 8s + 2s + 16s = 26s        (memo: 26s — reproduced)
M = |V| + 4D + 3(|E| + P)   ≤ 2s + 8s + 12s + 48s = 70s  (memo: 68s — corrected to 70s)
```

The memo's `68 s` is **not** claimed; the verified coarse bound is `70 s`.  The discrepancy
is a constant in a coarse upper bound and is irrelevant to every downstream statement, all
of which use only `q, M = O(s)`.

**Sharp constants (`SharpConstants.lean`).**  The memo's first graph identity is proved:

```text
Formula.toDag_numPairs :  P = 4a
```

(pair exclusions are created only by addition gates — two ordered out-pairs at the fresh
source, two ordered in-pairs at the fresh sink; the connector edges of `addDag` and
`mulDag` create none, because the source has in-degree zero and the sink out-degree zero).
Substituting it gives

```text
q = 2|E| + D + P ≤ 4l + 14a + 2u  ≤ 14 s     (Formula.rep2_numAux_le_sharp — memo's 14 s)
M = |V| + 4D + 3(|E|+P) ≤ 13l + 34a + 3u ≤ 34 s  (Formula.rep2_numFactors_le_sharp)
```

and `Formula.has_supportTwo_representation_sharp` packages both.  The memo's second
identity `D + B = 2a`, and the consequent `M ≤ 32 s`, are **not** proved: the number `D` of
degree-three vertices of a formula graph is not a function of `(l, a, u)` alone (it depends
on which children of a multiplication gate are addition gates), so the bound used here is
`D ≤ |V|`.

---

## E. Repairs, scope decisions and counterexample/firewall tests

**Repairs made.**

1. *Quadratic factors are not affine.*  Every edge selector `1 + z_a(ℓ_a+1)` and every pair
   exclusion `1 + z_a z_b` is expanded through the support-two gadget, with **one fresh
   auxiliary per occurrence**.
2. *Degree-three flow factors are not of support two.*  They are expanded through the
   ternary gadget, again with one fresh auxiliary per occurrence.  This is a new repair
   required by the support-two target and has no analogue in the support-three layer.
3. *The cubic error is killed pointwise only.*  Proof order: ternary identity → fix a
   Boolean selector assignment → use the same-head/same-tail exclusion → cancel the error
   → sum over the hypercube → conclude the `MvPolynomial` identity.  The generic compiler
   exposes this as an explicit hypothesis (`hkill`), so the order cannot be short-circuited.
4. *Pair exclusions at the source and sink are retained* (they come from the frozen
   selector polynomial, unchanged).
5. *Support ≤ 2 is claimed only for formula-generated graphs*, where labels are single
   variables or constants and the degree invariant holds.
6. *The memo constant `M ≤ 68 s` was corrected to the verified coarse `M ≤ 70 s`*; with the
   sharp pair count `P = 4a` the verified bounds become `q ≤ 14 s` and `M ≤ 34 s`.

**Firewall tests (all machine-checked, all negative results).**

| name | content |
| --- | --- |
| `cubic_error_not_formally_zero` | `abc(1+ab)` is not the zero polynomial |
| `ternary_error_nonzero_without_exclusion` | the ternary Boolean sum differs from `1+a+b+c` |
| `kappa_tau_zero_fails`, `kappa_tau_one_fails` | `τ = 0`, `τ = 1` break the gadget (hence `F₂` is out of scope) |
| `shared_one_bit_auxiliary_changes_result` | reusing one auxiliary across two gadgets changes the value |
| `unrestricted_label_supportTwo_firewall` | an edge labelled `x₁+x₂+x₃` yields a factor of support 4: SUPPORT2 is false for unrestricted ABPs |
| `single_variable_label_supportTwo` | with a one-variable label the gadget stays within support 2 |
| `degree_three_flow_factor_support_three` | a degree-three flow factor really has support 3, which is why the ternary gadget is needed |

**Gadget minimality (secondary, PARTIAL).**  Machine-checked:
`supportTwo_gadget_achieves_one_and_three` (one auxiliary, three factors, support ≤ 2,
Boolean sum `1 + xy`) and `zero_aux_needs_two_factors` (with no auxiliary at least two
affine factors are necessary, by total degree).  **Not** machine-checked, and therefore not
claimed: the full "zero auxiliary bits are impossible" statement (irreducibility of
`1 + X₀X₁`) and "two affine factors are impossible with one auxiliary bit".

---

## F. Build, axiom and placeholder audits

**Build.**  `lake build` completes successfully (8064 jobs, errors: none).  The new
support-two modules produce no warnings.

**Axioms.**  `AxiomAuditTwo.lean` runs `#print axioms` on all 52 principal theorems of the
layer (including two non-vacuity checks: the classes `VNP₁^{[≤2]}` and `VNP₁,BIZ` are
inhabited by a concrete family).  Every one reports a subset of

```text
propext, Classical.choice, Quot.sound
```

(the two denominator-free identities and `prod_add_err_mul` need only
`propext, Quot.sound`).  No project-specific axiom exists anywhere in `VNP1Char2`.

**Placeholders.**  A search of the whole `RequestProject/` tree for `sorry`, `admit`,
`axiom`, `native_decide`, `unsafe`, `opaque`, `@[implemented_by]` returns only occurrences
inside documentation comments (sentences stating that nothing is axiomatized, and the class
name `VNP1LE3`); there is no such declaration.

---

## G. What is machine-checked here versus imported literature

```text
MACHINE-CHECKED HERE
  the support-two ternary and 1+xy identities in characteristic two;
  the support-two DAG and formula compilers, with support ≤ 2 and O(size) bounds;
  the internal class equality N(VP_e(F)) = VNP₁^{[≤2]}(F);
  the bridge VNP₁^{[≤2]}(F) ⊆ VNP₁,BIZ(F) for the internal width-one-ABP class.

IMPORTED LITERATURE CONSEQUENCE (prose only, never axiomatized)
  Valiant's VNP_e = VNP;
  Bringmann–Ikenmeyer–Zuiddam's characteristic ≠ 2 theorem and their F₂ separation;
  hence the classification VNP₁(F) = VNP(F) ⟺ F ≇ F₂.
No Lean declaration of this project identifies any internal class with a literature class,
and no literature statement is assumed as an axiom.
```

---

## H. No P-vs-NP or runtime consequence

The compiler produces a *representation*: a hypercube sum of `O(s)` affine factors over
`O(s)` summed Boolean bits.  It provides **no** evaluator of that sum.  It therefore yields
no statement about `P` versus `NP`, `VP` versus `VNP`, no sub-`2^k` evaluator and no
algorithmic speedup.  The marker theorem
`supportTwo_scope_is_representation_only` records this formally.  No novelty claim is made.

---

## I. Strict final verdict

```text
VNP1 CHARACTERISTIC-TWO SUPPORT-TWO FORMALIZATION

TERNARY IDENTITY:                 PROVED
FORMAL-POLYNOMIAL STATUS:         PROVED (only the auxiliary bit is Boolean)
SUPPORT-TWO 1+xy GADGET:          PROVED (1 bit, 3 factors)
PROOF-ORDER FIREWALL:             PROVED (error killed pointwise, never formally)
SUPPORT-TWO PATH COMPILER:        PROVED
QUADRATIC→AFFINE GADGET EXPANSION: PROVED
TERNARY→AFFINE FLOW EXPANSION:    PROVED
SIZE ACCOUNTING:                  PROVED (coarse q ≤ 26 s, M ≤ 70 s; memo's 68 s corrected)
SHARP SIZE ACCOUNTING:            PROVED (P = 4a, q ≤ 14 s, M ≤ 34 s; D + B = 2a not proved)
SUPPORT ≤ 2:                      PROVED (formula-generated graphs only)
FINITE COMPILER THEOREM:          PROVED
FIELD SCOPE:                      [Field F], [CharP F 2], ∃ τ, τ ≠ 0 ∧ τ ≠ 1
                                  (finite case: 2 < Nat.card F; no F₄ subfield needed)
CLASS-LEVEL SUPPORT-TWO EQUALITY: PROVED (internal classes)
WIDTH-ONE-ABP BRIDGE:             PROVED (internal VNP₁,BIZ definition)
SHARP CONSTANTS:                  PARTIAL (P = 4a proved; D + B = 2a not proved)
GADGET MINIMALITY:                PARTIAL (achievement + zero-aux lower bound only)
P-vs-NP CONSEQUENCE:              NONE
FIRST REMAINING MATHEMATICAL OWNER: the memo's D + B = 2a (and with it M ≤ 32 s)
LAKE BUILD:                       PASS
PLACEHOLDER AUDIT:                PASS
AXIOM AUDIT:                      propext, Classical.choice, Quot.sound only
OVERALL:                          FORMALLY BANKABLE (support-two compiler and internal
                                  class equality); literature classification remains an
                                  external, non-formalized corollary
```
