# VNP1Char2 — FINAL BRIDGE REPAIR REPORT

Scope: a **small append-only certification repair** of the completed `VNP1Char2` project.
No banked proof was modified, reproved, optimised or replaced. Both completed
support-two compilers — the graph/path compiler and the direct formula-tree compiler —
are byte-for-byte unchanged (see §7).

```
STANDARD P-FAMILY DEGREE COVERAGE        PROVED
VNP1LE2 -> LITERAL BIZ-w+ SHAPED CLASS   PROVED
GRAPH COMPILER UNCHANGED                 YES
DIRECT COMPILER UNCHANGED                YES
WHOLE-PROJECT BUILD                      PASS
AXIOM AUDIT                              PASS
PLACEHOLDER AUDIT                        PASS
ARTIFACT REPORT/HASH                     UPDATED

FINAL BRIDGE REPAIR PASS
```

---

## 1. New files and exact new theorem names

All new material lives in three new modules plus a status file; the only edit to an
existing file is four appended `import` lines in the aggregator
`RequestProject/AlgebraicComplexity/VNP1Char2.lean`.

```
RequestProject/AlgebraicComplexity/VNP1Char2/PFamilyDegree.lean
RequestProject/AlgebraicComplexity/VNP1Char2/BIZWPlus.lean
RequestProject/AlgebraicComplexity/VNP1Char2/BridgeRepairAudit.lean
RequestProject/AlgebraicComplexity/VNP1Char2/BridgeRepairOwners.lean
```

Everything below is in namespace `VNP1Char2`, over `{F : Type} [Field F]`.

### 1.1 `PFamilyDegree.lean` — standard p-family total-degree condition

| name | statement |
|---|---|
| `PolyDegreeBounded` (def) | `PolyBounded fun n => (f.poly n).totalDegree` |
| `IsPFamily` (def) | `PolyBounded f.nvars ∧ PolyDegreeBounded f` — the standard p-family condition |
| `IsPFamily.nvars`, `IsPFamily.degree` | projections |
| `Formula.totalDegree_eval_le` | `(f.eval).totalDegree ≤ f.size` for every binary division-free arithmetic formula |
| `VPe.polyDegreeBounded` | `VPe f → PolyDegreeBounded f` |
| `VPe.isPFamily` | `VPe f → IsPFamily f` |
| `AffineForm.totalDegree_eval_le_one` | an affine form evaluated at polynomials of degree ≤ 1 has degree ≤ 1 |
| `AffineHypercubeRep.totalDegree_subst_le_one` | the hypercube substitution has degree ≤ 1 in every coordinate |
| `AffineHypercubeRep.totalDegree_value_le` | `R.value.totalDegree ≤ R.numFactors` — a product of `M` affine forms has degree ≤ `M`, and Boolean-hypercube summation does not increase the maximal degree in the original variables |
| `VNP1.polyDegreeBounded`, `VNP1.isPFamily` | `VNP1 f → IsPFamily f` |
| `VNP1LE3.isPFamily`, `VNP1LE2.isPFamily` | corollaries for the support-restricted classes |
| `totalDegree_aeval_le` | substituting every variable by a polynomial of total degree ≤ 1 does not raise the total degree |
| `totalDegree_witnessSubst_le_one` | the Boolean witness substitution has degree ≤ 1 in every coordinate |
| `NondetClosure.polyDegreeBounded`, `NondetClosure.isPFamily` | the nondeterministic closure of a class of standard p-families consists of standard p-families |
| `nondetVPe_isPFamily` | `NondetClosure VPe f → IsPFamily f` |
| `nondetVPe_eq_VNP1LE2_standard` | `(fun f => N(VP_e) f ∧ IsPFamily f) = (fun f => VNP₁^{[≤2]} f ∧ IsPFamily f)` |
| `nondetVPe_iff_VNP1LE2_isPFamily` | the pointwise `↔` form |
| `nondetVPe_subset_VNP1LE2_standard` | `N(VP_e) f → VNP₁^{[≤2]} f ∧ IsPFamily f` |
| `VNP1LE2_subset_nondetVPe_standard` | `VNP₁^{[≤2]} f → N(VP_e) f ∧ IsPFamily f` |
| `VPe_subset_VNP1LE2_standard` | `VP_e f → VNP₁^{[≤2]} f ∧ IsPFamily f` |

Field hypotheses of the class-level statements are unchanged: `[CharP F 2]`, `τ ≠ 0`,
`τ ≠ 1`. The degree theorems themselves need no characteristic hypothesis.

### 1.2 `BIZWPlus.lean` — the literal `w+` support-two bridge

| name | statement |
|---|---|
| `AffineForm.vars_termSum_subset` | the variables of `∑ cᵢ·X_{jᵢ}` lie among the listed `jᵢ` |
| `AffineForm.toPoly_vars_subset` | `A.toPoly.vars ⊆ A.vars` |
| `AffineForm.toPoly_vars_card_le` | `A.toPoly.vars.card ≤ A.numVars` — **the syntactic → semantic support bridge** |
| `VNP1BIZWPlus` (def) | hypercube sum over polynomially many witness bits of a product of polynomially many factors, each with **both** `totalDegree ≤ 1` **and** `vars.card ≤ 2` |
| `VNP1BIZWPlus.toVNP1BIZ` | forgetful inclusion `VNP₁,BIZ-w+(F) ⊆ VNP₁,BIZ(F)` |
| `VNP1LE2_subset_VNP1BIZWPlus` | **`VNP₁^{[≤2]}(F) ⊆ VNP₁,BIZ-w+(F)`** — the required literal bridge |
| `nondetVPe_subset_VNP1BIZWPlus` | `N(VP_e(F)) ⊆ VNP₁,BIZ-w+(F)` (char 2, `τ ≠ 0,1`) |
| `VPe_subset_VNP1BIZWPlus` | `VP_e(F) ⊆ VNP₁,BIZ-w+(F)` |
| `nondetVPe_subset_VNP1BIZWPlus_standard` | the same, together with `IsPFamily` |

### 1.3 `BridgeRepairAudit.lean`

| name | statement |
|---|---|
| `sampleFamily_isPFamily` | the concrete family `x₀` is a standard p-family (non-vacuity) |
| `sampleFamily_mem_VNP1BIZWPlus` | the concrete family `x₀` lands in the literal `w+` class (non-vacuity) |
| `totalDegree_one_not_supportTwo` | **firewall**: `x₀+x₁+x₂` over `ZMod 2` has total degree ≤ 1 but `vars.card = 3 > 2`, so `VNP1BIZWPlus` is strictly stronger than `VNP1BIZ` and the bridge really transports support information |
| `field_scope_marker` | the canonical positive hypothesis `∃ τ, τ ≠ 0 ∧ τ ≠ 1` suffices for the `w+` and p-family conclusions |

`BridgeRepairOwners.lean` records the two repaired items as closed and re-states that the
external literature results remain external.

---

## 2. Exact dependency graph

```
MainCompiler ──► PFamily ──► Nondeterminism ──► ClassLevel ─┐
MainCompilerTwo ────────────────────────────────────────────┴─► ClassLevelTwo
                                                                    │
                                                                    ▼
                                                             PFamilyDegree
                                                                    │
                                                                    ▼
                                                                BIZWPlus
                                                                    │
                        ClassLevelAudit ────────────────────────────┤
                                                                    ▼
                                                           BridgeRepairAudit
                                                                    │
                                                                    ▼
                                                          BridgeRepairOwners
```

Internal dependencies of the two principal new theorems:

* `nondetVPe_eq_VNP1LE2_standard`
  ← `nondetVPe_subset_VNP1LE2`, `VNP1LE2_subset_nondetVPe` (both frozen, `ClassLevelTwo`).
* `VNP1LE2_subset_VNP1BIZWPlus`
  ← `AffineForm.toPoly_totalDegree_le_one` (frozen, `ClassLevelTwo`),
    `AffineForm.toPoly_vars_card_le` (new),
    `AffineForm.card_vars_le`, `AffineForm.numVars_mapVar`, `AffineForm.aeval_toPoly`,
    `AffineForm.eval_mapVar` (frozen, `AffineForm` / `PFamily`),
    and the `SupportLE 2` component of the `VNP1LE2` hypothesis.
* `nondetVPe_isPFamily`
  ← `NondetClosure.polyDegreeBounded` ← `totalDegree_aeval_le`,
    `totalDegree_witnessSubst_le_one`, `VPe.polyDegreeBounded` ←
    `Formula.totalDegree_eval_le`.

No new dependency was added to any banked compiler theorem; the new modules import the
banked layer, not the other way round.

---

## 3. Repair 1 — standard p-family total-degree condition

**Gap.** `PolyFamily` and the internal classes `VPe`, `VNP1LE3`, `VNP1LE2`, `VNP1`,
`NondetClosure` encode *polynomially many variables* structurally (the `n`-th member has
variable type `Fin (nvars n)` with `PolyBounded nvars`), but they do **not** literally
encode the second half of the standard literature p-family definition: *polynomially
bounded total degree*. In this precise sense the internal classes are **broader** than
the standard literature universe.

**Repair.** `PFamilyDegree.lean` introduces `PolyDegreeBounded` and `IsPFamily` and proves
that the gap is empty for every family occurring in the existing theorem:

* formula side: `deg(f) ≤ size(f)` (`Formula.totalDegree_eval_le`, by structural
  induction: `deg(X) = 1`, `deg(C) = 0`, `deg(p+q) ≤ max`, `deg(p·q) ≤ deg p + deg q`),
  hence `VPe.isPFamily`;
* affine-product side: `deg(∏_{j≤M} L_j) ≤ M` and hypercube summation does not raise the
  maximal degree (`AffineHypercubeRep.totalDegree_value_le`, via
  `totalDegree_finsetSum_le` and `totalDegree_list_prod`), hence `VNP1.isPFamily` and the
  corollaries `VNP1LE3.isPFamily`, `VNP1LE2.isPFamily` — this covers **every family used
  in the reverse containment `VNP₁^{[≤2]} ⊆ N(VP_e)`**;
* witness side: `totalDegree_aeval_le` (substituting degree-≤1 polynomials does not raise
  degree) gives `NondetClosure.isPFamily` and `nondetVPe_isPFamily`.

**Which new theorem restricts the main result back to standard p-families.**
`nondetVPe_eq_VNP1LE2_standard` (with the pointwise form
`nondetVPe_iff_VNP1LE2_isPFamily` and the two directional forms
`nondetVPe_subset_VNP1LE2_standard`, `VNP1LE2_subset_nondetVPe_standard`). Because
`VPe.isPFamily`, `VNP1LE2.isPFamily` and `nondetVPe_isPFamily` hold unconditionally, the
restriction is *not* a weakening: both sides of the internal equality already consist of
standard p-families.

**Not done (deliberately, per the non-goals).** The class hierarchy was not redesigned;
`PolyFamily`, `VPe`, `VNP1LE2`, `VNP1LE3`, `VNP1`, `NondetClosure` are untouched.

---

## 4. Repair 2 — literal BIZ `w+` bridge

**Gap.** The internal class `VNP1BIZ` requires only `P.totalDegree ≤ 1` of each factor.
That is an unrestricted affine width-one representation and does not encode the `w+`
requirement that every affine edge label involve at most two variables. The firewall
`totalDegree_one_not_supportTwo` exhibits a concrete degree-one polynomial
(`x₀ + x₁ + x₂`) with three variables, so the two conditions are genuinely different.

**Repair.** The new class `VNP1BIZWPlus` requires of every factor **both**
`P.totalDegree ≤ 1` **and** `P.vars.card ≤ 2`. The existing `VNP1BIZ` was not renamed and
not modified; `VNP1BIZWPlus.toVNP1BIZ` is the forgetful inclusion.

The bridge `VNP1LE2_subset_VNP1BIZWPlus` consumes the already-certified *syntactic*
`SupportLE 2` property of the compiled representations — every affine factor has at most
two `(coefficient, variable)` terms — and converts it into the *semantic* condition of the
literature-shaped class through the new chain

```
A.toPoly.vars ⊆ A.vars            (AffineForm.toPoly_vars_subset)
A.vars.card   ≤ A.numVars         (AffineForm.card_vars_le, frozen)
⇒ A.toPoly.vars.card ≤ A.numVars  (AffineForm.toPoly_vars_card_le)
```

applied after the aux-renaming `mapVar (ρ n)`, whose `numVars` invariance is the frozen
`AffineForm.numVars_mapVar`. No external BIZ theorem is imported, as an axiom or
otherwise.

---

## 5. Repair 3 — field-scope hygiene

Inspection of the whole Lean source for `F₂`-shaped hypotheses: the only occurrence of the
two-element field in a Lean *statement* is
`VNP1Char2.ringEquiv_zmod_two_of_card_eq_two : Nat.card F = 2 → Nonempty (ZMod 2 ≃+* F)`
(frozen, `ClassLevel.lean`), which is a ring **isomorphism** statement, recorded for
completeness and not used as a hypothesis anywhere. All other `F₂` mentions are prose in
docstrings and status files.

No theorem uses type equality or type inequality with `F₂` as a substitute for field
isomorphism. The canonical positive hypothesis remains `∃ τ : F, τ ≠ 0 ∧ τ ≠ 1` (which
covers infinite characteristic-two fields); the finite statements `2 < Nat.card F` /
`2 < Fintype.card F` occur only as corollaries feeding that hypothesis.

**Conclusion: no mathematical change required.** The `F ≠ F₂` phrasing is a manuscript
wording issue only. `field_scope_marker` records the canonical hypothesis in Lean.

---

## 6. Build result

```
$ lake build
Build completed successfully (8075 jobs).
```

Errors: none. Warnings from the four new modules: none (the remaining warnings in the
build log are the pre-existing linter warnings of the frozen layer, unchanged).

---

## 7. Frozen-compiler check

`git status` after the repair shows exactly:

```
 M RequestProject/AlgebraicComplexity/VNP1Char2.lean       (4 appended import lines only)
?? RequestProject/AlgebraicComplexity/VNP1Char2/PFamilyDegree.lean
?? RequestProject/AlgebraicComplexity/VNP1Char2/BIZWPlus.lean
?? RequestProject/AlgebraicComplexity/VNP1Char2/BridgeRepairAudit.lean
?? RequestProject/AlgebraicComplexity/VNP1Char2/BridgeRepairOwners.lean
```

In particular `GraphCompilerTwo.lean`, `CompilerTwo.lean`, `MainCompilerTwo.lean`,
`PathSelector.lean`, `PathTheorem.lean`, `FormulaToDAG.lean`, `DirectBranchGadget.lean`,
`DirectFormulaCompiler.lean`, `DirectClassLevelTwo.lean`, `ClassLevel.lean`,
`ClassLevelTwo.lean` and all audit files are unmodified, and the existing direct-proof
independence audit (`AxiomAuditDirect.lean`, transitive-dependency firewall) is preserved
and still passes. No banked proof was altered to reduce imports.

---

## 8. Axiom result

`#print axioms` is run in `BridgeRepairAudit.lean` on every new principal theorem
(18 from `PFamilyDegree`, 7 from `BIZWPlus`, 4 audit-layer statements). **Every one reports
exactly**

```
[propext, Classical.choice, Quot.sound]
```

No project-specific axiom exists anywhere in the project.

---

## 9. Placeholder result

Search of the four new files for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`opaque`, `@[implemented_by]`: **no declarations and no occurrences at all**.
Tree-wide, the only matches are the substring "admitting" inside docstrings and prose
sentences stating that nothing is axiomatized. `decide` is used once, on a closed
three-element `Finset` cardinality inside the firewall `totalDegree_one_not_supportTwo`;
no universal theorem depends on finite enumeration.

```
PLACEHOLDER AUDIT: PASS
```

---

## 10. Artifact metadata

* Git commit of the repaired package: `ce4faea57ea2a5c667912521bb0c265da6635f92`
  (tree `1c250764186f1b41eaf1d29c86f85215a66717e2`).
* No distributable archive was produced in this run, so no archive SHA-256 is quoted.
  SHA-256 of the files that changed:

```
f732433f98113e3229372cd6f799d8fd9fe64a02b05f6ac3a462bc048fcae711  RequestProject/AlgebraicComplexity/VNP1Char2/PFamilyDegree.lean
8d9dda5118adb757ae6c95fcbe30e9ed1ea28282e47ad55ed3cf9b6db6c72774  RequestProject/AlgebraicComplexity/VNP1Char2/BIZWPlus.lean
61b597b8ee5874e2eb88d79a6eef77e63a0bbbda47482ea4de0aec36327f3568  RequestProject/AlgebraicComplexity/VNP1Char2/BridgeRepairAudit.lean
abdd1d718cea2be77a3ae1cebd2f5e18872e5b54375b8f90519fe481120d86bb  RequestProject/AlgebraicComplexity/VNP1Char2/BridgeRepairOwners.lean
d9e8ae92163da44d70bf20416da709e69d954e820e06c2be10d98817e06e9a85  RequestProject/AlgebraicComplexity/VNP1Char2.lean
```

**Any previously published manuscript artifact hash is stale**: it predates this repair and
does not match the repaired package. The artifact identifier to quote is the commit above.

---

## 11. Scope discipline (unchanged)

* No new compiler, no gadget-minimality work, no change to the `14s, 34s` or `2s, 9s/2`
  accounting, no border width two, no VP-vs-VNP, no novelty claim.
* Valiant's theorem and the Bringmann–Ikenmeyer–Zuiddam characteristic-not-two and `F₂`
  results remain **IMPORTED LITERATURE CONSEQUENCE**, stated in prose only; nothing of them
  is formalized or axiomatized here.
* This layer is a certification layer about representations and classes. It supplies no
  evaluator, and therefore no P-vs-NP, VP-vs-VNP or runtime consequence is claimed.

---

## 12. Strict final verdict

```
STANDARD P-FAMILY DEGREE COVERAGE        PROVED
  formula degree bound                   PROVED  (deg f ≤ size f)
  affine-product degree bound            PROVED  (deg ≤ M, hypercube sum non-increasing)
  witness-substitution degree bound      PROVED
  standard-universe class corollaries    PROVED
VNP1LE2 -> LITERAL BIZ-w+ SHAPED CLASS   PROVED  (VNP1LE2_subset_VNP1BIZWPlus)
  forgetful VNP1BIZWPlus -> VNP1BIZ      PROVED
  w+ strictly stronger than degree-only  PROVED  (firewall)
FIELD SCOPE                              ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1, [Field F], [CharP F 2]
                                         (no type-level F₂ statement exists; manuscript
                                          wording only)
GRAPH COMPILER UNCHANGED                 YES
DIRECT COMPILER UNCHANGED                YES
WHOLE-PROJECT BUILD                      PASS
AXIOM AUDIT                              PASS  ([propext, Classical.choice, Quot.sound])
PLACEHOLDER AUDIT                        PASS
ARTIFACT REPORT/HASH                     UPDATED
FIRST REMAINING MATHEMATICAL OWNER       NONE (within the scope of this repair)

FINAL BRIDGE REPAIR PASS
```
