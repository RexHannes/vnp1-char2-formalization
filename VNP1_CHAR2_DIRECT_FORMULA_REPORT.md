# The direct formula-tree activation compiler — formalization report

Append-only second proof of the characteristic-two **support-two** compiler, independent of
the frozen graph/path layer.  No existing mathematical declaration was modified, renamed,
weakened or reproved; the only edit to an existing file is seven appended `import` lines in
the aggregator `RequestProject/AlgebraicComplexity/VNP1Char2.lean`.

---

## A. Status block

```text
BRANCH GADGET (Boolean identity)          PROVED
SUPPORT OF EVERY BRANCH FACTOR ≤ 2        PROVED
DIRECT FORMULA SEMANTICS (SEM)            PROVED
DIRECT FINITE COMPILER                    PROVED
SUPPORT ≤ 2 (whole representation)        PROVED
q ≤ 2s   (exact: q = 2l + 2a + u)         PROVED
2M ≤ 9s  and  M ≤ 5s                      PROVED
          (exact: M = 1 + 3l + 6a + 2u)
FRESHNESS / CUBE FLATTENING               PROVED
DIRECT CLASS FORWARD CONTAINMENT          PROVED
            N(VP_e(F)) ⊆ VNP₁^{[≤2]}(F)
INDEPENDENCE FROM GRAPH/PATH PROOF        MACHINE-CHECKED (dependency scan)
LAKE BUILD                                PASS
AXIOM AUDIT                               propext, Classical.choice, Quot.sound only
PLACEHOLDER AUDIT                         PASS (no sorry/admit/axiom/native_decide/
                                          unsafe/opaque/@[implemented_by])
P-vs-NP / VP-vs-VNP CONSEQUENCE           NONE
VERDICT                                   DIRECT FORMULA-TREE COMPILER BANKED
```

Field scope everywhere: `[Field F]`, `[CharP F 2]`, and an element `τ : F` with `τ ≠ 0`,
`τ ≠ 1` (equivalently, for finite fields, `2 < Nat.card F`).  Infinite characteristic-two
fields are covered, and no `F₄` subfield is required (`GF(8)` instance included).

---

## B. New files

```text
RequestProject/AlgebraicComplexity/VNP1Char2/DirectBranchGadget.lean
RequestProject/AlgebraicComplexity/VNP1Char2/DirectFormulaCompiler.lean
RequestProject/AlgebraicComplexity/VNP1Char2/DirectClassLevelTwo.lean
RequestProject/AlgebraicComplexity/VNP1Char2/TwoPointWeights.lean
RequestProject/AlgebraicComplexity/VNP1Char2/RegressionTestsDirect.lean
RequestProject/AlgebraicComplexity/VNP1Char2/AxiomAuditDirect.lean
RequestProject/AlgebraicComplexity/VNP1Char2/DirectCompilerOwners.lean
```

---

## C. The construction

With `κ = τ(τ+1)` (`kappaVal`), the **branch gadget** is the product of six affine factors

| factor | variables |
|---|---|
| `1 + (1 + κ⁻¹) h` | `h` |
| `c + τ h` | `c, h` |
| `c + (τ+1) h` | `c, h` |
| `1 + ((τ+1)/τ) b + (1/τ) h` | `b, h` |
| `1 + (τ/(τ+1)) a + (1/(τ+1)) h` | `a, h` |
| `1 + τ a + (τ+1) b` | `a, b` |

each of support ≤ 2, with one fresh Boolean auxiliary `h`.

Every syntax node `v` gets a fresh activation bit `z_v`.

* **root**: the unary factor `z_root` (pins the root active);
* **multiplication** `v = u·w`: `1 + z_v + z_u` and `1 + z_v + z_w`  (on Boolean values in
  characteristic two, `1 + x + y` is the equality indicator, so both children inherit the
  parent's state);
* **addition** `v = u + w`: the branch gadget with `a = z_u`, `b = z_w`, `c = z_v` and one
  fresh bit;
* **leaf** with label `ℓ`: `1 + z_v(ℓ+1)`, expanded by the banked one-bit three-factor
  gadget `gadget2Factors` with `x = ℓ+1`, `y = z_v` and one fresh bit.

Auxiliary index types are built by structural recursion out of disjoint sums
(`Formula.Aux`, `Formula.TAux`), so freshness holds *by construction*: two equal-shaped
subformulas own disjoint coordinates.

---

## D. Exact theorem list (all in namespace `VNP1Char2`)

| name | file | statement |
|---|---|---|
| `branch_identity` | `DirectBranchGadget` | for Boolean `a,b,c`: `∑_{h∈{0,1}} Γ_τ(a,b,c;h) = (1+a+b+c)(1+ab)` |
| `BranchAllowed`, `branch_truth_table` | `DirectBranchGadget` | the sum is `1` exactly on `(0,0,0), (1,0,1), (0,1,1)` and `0` on the other five states |
| `numVars_branchFactors_le` | `DirectBranchGadget` | every branch factor has support ≤ 2 |
| `prod_branchFactors`, `sum_prod_branchFactors` | `DirectBranchGadget` | the gadget inside any commutative `F`-algebra |
| `sum_cube_sum`, `sum_cube_unit`, `sum_prod_split` | `DirectFormulaCompiler` | cube flattening along disjoint sums |
| `one_add_boolVal_add_boolVal` | `DirectFormulaCompiler` | `1 + x + y` is the Boolean equality indicator in characteristic two |
| `Formula.Aux`, `Formula.TAux`, `Formula.bodyFactors`, `Formula.condZ` | `DirectFormulaCompiler` | fresh auxiliaries, factors, conditioned partition function |
| `Formula.card_taux` | `DirectFormulaCompiler` | `q = 2l + 2a + u` |
| `Formula.length_bodyFactors` | `DirectFormulaCompiler` | body factor count `3l + 6a + 2u` |
| `Formula.numVars_bodyFactors_le` | `DirectFormulaCompiler` | every compiled factor has support ≤ 2 |
| `Formula.condZ_var`, `condZ_const`, `condZ_mul`, `condZ_add` | `DirectFormulaCompiler` | the four node rules |
| `Formula.condZ_spec` | `DirectFormulaCompiler` | **(SEM)** `Z_f(0) = 1`, `Z_f(1) = f.eval` |
| `Formula.directRep`, `directRep_value` | `DirectFormulaCompiler` | the representation and its correctness |
| `Formula.directRep_supportLE_two` | `DirectFormulaCompiler` | `SupportLE 2` |
| `Formula.directRep_numAux`, `directRep_numFactors` | `DirectFormulaCompiler` | `q = 2l+2a+u`, `M = 1+3l+6a+2u` |
| `Formula.leaves_eq_gates_succ` | `DirectFormulaCompiler` | `l = a + u + 1` |
| `Formula.directRep_numAux_le`, `directRep_numAux_eq_two_size_sub` | `DirectFormulaCompiler` | `q ≤ 2s`, `q = 2s − u` |
| `Formula.directRep_two_numFactors_le`, `directRep_numFactors_le` | `DirectFormulaCompiler` | `2M ≤ 9s`, `M ≤ 5s` |
| `Formula.has_supportTwo_representation_direct` | `DirectFormulaCompiler` | **main finite direct compiler theorem** |
| `Formula.has_supportTwo_representation_direct_of_exists_tau` | `DirectFormulaCompiler` | same under `∃ τ ≠ 0,1` |
| `nondetVPe_subset_VNP1LE2_direct` | `DirectClassLevelTwo` | **`N(VP_e(F)) ⊆ VNP₁^{[≤2]}(F)`**, direct proof |
| `VPe_subset_VNP1LE2_direct` | `DirectClassLevelTwo` | `VP_e ⊆ VNP₁^{[≤2]}` |
| `nondetVPe_eq_VNP1LE2_direct` (+ `_of_exists_tau`, `_of_natCard`) | `DirectClassLevelTwo` | internal class equality (reverse containment reused) |
| `nondetVPe_subset_VNP1BIZ_direct` | `DirectClassLevelTwo` | through the banked width-one bridge |
| `two_point_identity` (+ moment lemmas, `muVal_tau_succ`) | `TwoPointWeights` | optional §8 identity |
| `branch_unrestricted_fails` | `RegressionTestsDirect` | scope firewall (see F) |
| `Formula.has_supportTwo_representation_direct_GF4/GF8/GF16` | `RegressionTestsDirect` | concrete fields |

Dependencies of the main chain:

```text
branch_identity → branch_truth_table → sum_prod_branchFactors
        ↓
condZ_add ─┐
condZ_mul ─┤→ condZ_spec → directRep_value → has_supportTwo_representation_direct
condZ_var ─┤                                        ↓
condZ_const┘                       nondetVPe_subset_VNP1LE2_direct
```

Only the shared data types (`Formula`, `AffineForm`, `AffineHypercubeRep`), the banked
`1 + x y` gadget `gadget2Factors` / `twoFactor_identity`, and `kappa_ne_zero` are imported
from the existing bank.

---

## E. Independence from the frozen graph/path proof

`AxiomAuditDirect.lean` contains a **machine-checked dependency scan**: it collects the
transitive constant dependencies of `Formula.has_supportTwo_representation_direct` and of
`nondetVPe_subset_VNP1LE2_direct` and raises an elaboration error if any of

```text
Formula.rep2_value
Formula.has_supportTwo_affineHypercubeRepresentation
Formula.has_supportTwo_representation_of_exists_tau
PathGraph.graphRep2_value
PathGraph.graphRep2_supportLE_two
Formula.toDag_value
nondetVPe_subset_VNP1LE2
```

occurs.  The build prints

```text
independence firewall: the direct theorems use no graph/path correctness theorem
```

The frozen theorems that *are* reused, and only after the new forward containment, are the
reverse containment `VNP1LE2_subset_nondetVPe` and the literature-shaped width-one bridge
`VNP1LE2_subset_VNP1BIZ`.

---

## F. Regression tests and firewalls (`RegressionTestsDirect.lean`)

1. branch truth table for all eight states; exactly three allowed states (`decide`);
2. leaves `x₀` and `1`;
3.–5. `x₀ + x₁`, `x₀ * x₁`, `(x₀+x₁)*x₂`, `x₀ + x₁*x₂`, `(x₀+1)*(x₁+x₂)`;
6. compiled value equals the formula polynomial in every case;
7. support ≤ 2 on the mixed examples;
8.–9. exact counts: `(x₀+x₁)*x₂` gives `q = 9`, `M = 18`; `(x₀+1)*(x₁+x₂)` gives `q = 13`,
   `M = 27`; and the general bounds instantiated;
10. freshness: for `(x₀+x₁)*(x₀+x₁)` the auxiliary count is `2·6 + 1 = 13`, i.e. the two
    equal-shaped copies do **not** share bits (sharing would give `7`);
* concrete fields `GF(4)`, `GF(8)`, `GF(16)`.

**Scope firewall.**  `branch_unrestricted_fails` proves that for `κ ≠ 1` and a parent value
`c ∉ {0,1}` the branch sum differs from `(1+a+b+c)(1+ab)` by `(1+κ⁻¹)c(c+1) ≠ 0`.  Hence
`(BRANCH)` is a Boolean-semantic identity only, and is stated and used only for Boolean
arguments.  The frozen layer's own firewalls (τ = 0, τ = 1, auxiliary reuse, unrestricted
ABP labels) are untouched.

---

## G. Build, axiom and placeholder audits

* `lake build` on the whole project: **Build completed successfully** (no errors; only
  pre-existing linter warnings from older files).
* `#print axioms` on all principal new theorems (`AxiomAuditDirect.lean`): every one
  reports a subset of `propext`, `Classical.choice`, `Quot.sound`.
* Placeholder search over the new files for `sorry`, `admit`, `axiom`, `native_decide`,
  `unsafe`, `opaque`, `@[implemented_by]`: no declaration; the only textual hits are
  documentation sentences stating that nothing is axiomatized.

---

## H. Separation of claims

**Machine-checked here** — the branch-gadget Boolean identity and its truth table; support
≤ 2 of every factor; the direct formula-tree activation semantics; direct compiler
correctness as an identity of polynomials in the original variables; freshness and cube
flattening; `q ≤ 2s`; `2M ≤ 9s` and `M ≤ 5s`; the direct forward containment
`N(VP_e(F)) ⊆ VNP₁^{[≤2]}(F)`; the build, axiom, placeholder and independence audits.

**Reused frozen theorems** — the graph/path support-two compiler (independent cross-check,
not used in the direct proof); the reverse class containment; the literature-shaped
width-one bridge.

**External literature only, not formalized and not axiomatized** — Valiant's
`VNP_e = VNP`; Bringmann–Ikenmeyer–Zuiddam's characteristic-not-two theorem and their `F₂`
separation.  If (and only if) the internal definitions of this project are confirmed to
match the literature definitions, the formal theorems above would support the proposed
classification `VNP₁(F) = VNP(F) ⟺ F ≇ F₂`; that synthesis remains prose, not a Lean
theorem.

**No runtime consequence.**  The layer produces a representation, not an evaluator: it
implies no `P = NP`, `P ≠ NP`, `VP = VNP`, `VP ≠ VNP`, and no algorithmic speedup.  No
novelty claim is made.

---

## I. Final verdict

```text
DIRECT FORMULA-TREE COMPILER: BANKED
FIRST REMAINING MATHEMATICAL OWNER: NONE for the direct route
  (open, not attempted: minimality of the six-factor branch gadget; identification of the
   internal classes with the literature classes)
```
