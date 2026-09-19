# VNP₁ characteristic-two formalization — class-level layer

This report covers the **new, strictly append-only class-level layer** added on top of the
existing `VNP1Char2` kernel bank.  No file of the existing layer was modified, renamed,
weakened or reproved; the only edit to an existing file is the addition of five `import`
lines at the end of the aggregator `RequestProject/AlgebraicComplexity/VNP1Char2.lean`.

---

## A. Status block

```text
FINITE COMPILER:
    BANK  (unchanged: Formula.has_supportThree_affineHypercubeRepresentation)

CLASS-LEVEL VP_e → VNP1[≤3]:
    PROVED   (VNP1Char2.VPe_subset_VNP1LE3)

N(VP_e) → VNP1[≤3]:
    PROVED   (VNP1Char2.nondetVPe_subset_VNP1LE3)

VNP1[≤3] → N(VP_e):
    PROVED   (VNP1Char2.VNP1LE3_subset_nondetVPe)

INTERNAL FORMULA-VNP = VNP1[≤3]:
    PROVED   (VNP1Char2.nondetVPe_eq_VNP1LE3)

STANDARD VNP IDENTIFICATION:
    EXTERNAL LITERATURE COROLLARY ONLY (not formalized, not axiomatized)

CHAR-2 |F|>2 OPEN CASE:
    MATHEMATICAL CORE CLOSED, internally: the class bridge is machine-checked for every
    field of characteristic two carrying an element τ ≠ 0, 1.  The identification of the
    internal classes with the literature classes is NOT formalized.

SUPPORT-TWO:
    OPEN (not attempted)

P vs NP / VP vs VNP:
    NO CONSEQUENCE
```

---

## B. New files

```text
RequestProject/AlgebraicComplexity/VNP1Char2/PFamily.lean
RequestProject/AlgebraicComplexity/VNP1Char2/Nondeterminism.lean
RequestProject/AlgebraicComplexity/VNP1Char2/ClassLevel.lean
RequestProject/AlgebraicComplexity/VNP1Char2/ClassLevelAudit.lean
RequestProject/AlgebraicComplexity/VNP1Char2/ClassLevelOwners.lean
```

---

## C. Glossary (definitions)

| name | file | meaning |
|---|---|---|
| `VNP1Char2.PolyBounded p` | `PFamily.lean` | `∃ c k, ∀ n, p n ≤ c * (n+1)^k` — an explicit elementary polynomial bound. |
| `VNP1Char2.PolyFamily F` | `PFamily.lean` | `nvars : ℕ → ℕ` together with `poly : ∀ n, MvPolynomial (Fin (nvars n)) F`.  Using a finite variable index type per `n` makes "polynomially many variables" the structural condition `PolyBounded nvars`. |
| `VNP1Char2.VPe f` | `PFamily.lean` | `PolyBounded f.nvars` and a formula family `φ n : Formula (Fin (f.nvars n)) F` with `(φ n).eval = f.poly n` and `(φ n).size ≤ s n`, `s` polynomially bounded. |
| `VNP1Char2.VNP1LE3 f` | `PFamily.lean` | `PolyBounded f.nvars` and representations `R n : AffineHypercubeRep (Fin (f.nvars n)) F` with `(R n).Represents (f.poly n)`, `(R n).SupportLE 3`, `numAux ≤ q n`, `numFactors ≤ M n`, `q`, `M` polynomially bounded. |
| `VNP1Char2.VNP1 f` | `PFamily.lean` | the same without the support-three requirement. |
| `VNP1Char2.witnessSubst m k b` | `Nondeterminism.lean` | substitution keeping the first `m` variables and sending the next `k` to the Boolean witness bits `b`. |
| `VNP1Char2.NondetClosure C f` | `Nondeterminism.lean` | BIZ Definition 2.2: `f_n(x) = ∑_{b∈{0,1}^{p(n)}} g_{q(n)}(b,x)` with `g ∈ C`, `p`, `q` polynomially bounded and `g.nvars (q n) ≤ f.nvars n + p n`. |
| `VNP1Char2.VNPe f` | `Nondeterminism.lean` | `NondetClosure VPe f`. |

Support is counted by `AffineForm.numVars`, the length of the coefficient/variable list of
the factor, over **all** its variables — original variables and hypercube variables alike
(the factors live over `ι ⊕ aux`).

---

## D. Theorem list

| name | file | statement | main dependencies |
|---|---|---|---|
| `PolyBounded.add`, `PolyBounded.const_mul`, `PolyBounded.comp`, `PolyBounded.mono`, `polyBounded_const`, `polyBounded_id` | `PFamily.lean` | closure properties of the polynomial bound (in particular closure under composition, which is what keeps `s (q n)` polynomial in `n`). | — |
| `AffineForm.toFormula_eval`, `AffineForm.toFormula_size` | `PFamily.lean` | an affine form is a formula computing `A.toPoly`, of size exactly `4·numVars + 1`. | — |
| `Formula.prodList_eval`, `Formula.prodList_size`, `Formula.prodList_size_le` | `PFamily.lean` | a product of finitely many formulas is a formula, `size = ∑(size+1)+1`. | — |
| `AffineForm.map_eval` | `PFamily.lean` | an `F`-algebra map commutes with evaluation of an affine form. | — |
| `AffineHypercubeRep.reindex`, `reindex_value`, `reindex_numAux`, `reindex_numFactors`, `reindex_supportLE` | `PFamily.lean` | renaming all variables of a representation: value, sizes and support bound. | `AffineForm.eval_mapVar` |
| `witnessSubst_eq_elim`, `witnessSubst_zero` | `Nondeterminism.lean` | the witness substitution as a `Sum.elim`, and its triviality for an empty cube. | — |
| `subset_nondetClosure`, `NondetClosure.mono`, `VPe.toVNPe` | `Nondeterminism.lean` | `C ⊆ N(C)` (empty cube), monotonicity, `VP_e ⊆ VNP_e`. | — |
| `Formula.rep_numAux_le_size`, `Formula.rep_numFactors_le_size` | `ClassLevel.lean` | `numAux ≤ 44·size f`, `numFactors ≤ 84·size f` for the banked compiled representation. | `Formula.rep_numAux_le`, `Formula.rep_numFactors_le` (existing) |
| `AffineHypercubeRep.aeval_value` | `ClassLevel.lean` | substituting polynomials for the original variables commutes with the hypercube sum. | `AffineForm.map_eval` |
| `elim_comp_nondetRho` | `ClassLevel.lean` | the merged assignment on the flattened cube equals the pair (witness substitution, gadget assignment). | `witnessSubst_eq_elim` |
| **`nondetVPe_subset_VNP1LE3`** | `ClassLevel.lean` | `[CharP F 2]`, `τ ≠ 0`, `τ ≠ 1` ⊢ `NondetClosure VPe f → VNP1LE3 f`. | `Formula.rep_value`, `Formula.rep_supportLE_three`, the two size lemmas, `reindex_*`, `aeval_value`, `Equiv.sumArrowEquivProdArrow` |
| **`VPe_subset_VNP1LE3`** | `ClassLevel.lean` | `[CharP F 2]`, `τ ≠ 0`, `τ ≠ 1` ⊢ `VPe f → VNP1LE3 f`. | `VPe.toVNPe`, `nondetVPe_subset_VNP1LE3` |
| **`VNP1LE3_subset_nondetVPe`** | `ClassLevel.lean` | `VNP1LE3 f → NondetClosure VPe f` (no characteristic hypothesis needed). | `toFormula_*`, `prodList_*`, `witnessSubst_comp_repRho` |
| **`nondetVPe_eq_VNP1LE3`** | `ClassLevel.lean` | `N(VP_e(F)) = VNP₁^{[≤3]}(F)` as predicates on `PolyFamily F`. | the two containments |
| `nondetVPe_subset_VNP1` | `ClassLevel.lean` | `N(VP_e(F)) ⊆ VNP₁(F)`. | `VNP1LE3.toVNP1` |
| `nondetVPe_eq_VNP1LE3_of_exists_tau` | `ClassLevel.lean` | the class equality under `∃ τ, τ ≠ 0 ∧ τ ≠ 1` (covers infinite fields). | — |
| `nondetVPe_eq_VNP1LE3_of_natCard` | `ClassLevel.lean` | the class equality for finite `F` with `2 < Nat.card F`. | existing `exists_tau_of_two_lt_natCard` |
| `ringEquiv_zmod_two_of_card_eq_two` | `ClassLevel.lean` | a characteristic-two field with exactly two elements is `ZMod 2`.  Recorded for completeness; used by nothing. | `ZMod.ringEquiv` |
| `sampleFamily_mem_VPe`, `sampleFamily_mem_VNP1LE3` | `ClassLevelAudit.lean` | non-vacuity: a concrete family lies in `VP_e`, hence in `VNP₁^{[≤3]}`. | `VPe_subset_VNP1LE3` |
| `classLevel_scope_is_representation_only` | `ClassLevelOwners.lean` | marker theorem: membership yields only representations, no evaluator. | `nondetVPe_subset_VNP1LE3` |

### Dependency graph (new layer)

```text
MainCompiler (existing bank)
      │
   PFamily ──────────────┐
      │                  │
 Nondeterminism          │
      │                  │
  ClassLevel  ◀──── FieldCorollary (existing)
      │
 ClassLevelAudit
      │
 ClassLevelOwners
```

---

## E. Audit of the load-bearing theorem `nondetVPe_subset_VNP1LE3`

* **Original witness bits remain variables of the compiled formula.**  The inner family
  `g_{q(n)}` is a polynomial in `Fin (g.nvars (q n))` variables; the side condition
  `g.nvars (q n) ≤ f.nvars n + p n` guarantees every such variable is either one of the
  `f.nvars n` original variables or one of the `p n` witness bits.  The formula `φ (q n)`
  for `g_{q(n)}` is compiled *with the witness bits as ordinary variables*.
* **Fresh compiler auxiliaries are disjoint.**  The merged cube is indexed by the disjoint
  union `Fin (p n) ⊕ ((φ (q n)).rep τ).aux`; the renaming `nondetRho` sends the witness
  variables to the left summand and the compiler auxiliaries to the right summand, so no
  auxiliary of one gadget is ever identified with another bit.
* **No unused Boolean variable is introduced.**  The flattening introduces no new summed
  bit at all: the cube is exactly the union of the given witness cube and the compiler's
  own cube.  (The firewall `sum_bool_one` in the existing layer records why an unused
  summed bit would be fatal in characteristic two.)
* **Support ≤ 3 survives.**  The renaming is applied factorwise by `AffineForm.mapVar`,
  which preserves `numVars` (`AffineForm.numVars_mapVar`), hence
  `AffineHypercubeRep.reindex_supportLE`.
* **Both witness dimensions remain polynomial.**  Cube dimension `p n + 44·size(φ (q n)) ≤
  p n + 44·s (q n)`, factor count `84·size(φ (q n)) ≤ 84·s (q n)`; `s ∘ q` is polynomially
  bounded by `PolyBounded.comp`, so uniformity is machine-checked, not assumed.
* **The flattening is not handwaved.**  The interchange
  `∑_{w : A ⊕ B → Bool} = ∑_{b}∑_{u}` is carried out through the explicit equivalence
  `Equiv.sumArrowEquivProdArrow` and `Fintype.sum_prod_type`; the false step
  `(∑_b A_b)(∑_c B_c) = ∑_b A_b B_b` is nowhere used (and is refuted by the existing
  firewall `shared_auxiliary_changes_result`).

For the reverse containment, the support-three hypothesis is what makes each affine factor
a formula of size `4·numVars + 1 ≤ 13`, so the whole product is a formula of size at most
`14·M n + 1` — polynomially bounded.

---

## F. Field scope

The class theorems assume

```lean
[Field F] [CharP F 2]        and       τ : F, τ ≠ 0, τ ≠ 1
```

exactly as the banked finite compiler does.  The canonical packaged hypothesis is
`∃ τ : F, τ ≠ 0 ∧ τ ≠ 1` (`nondetVPe_eq_VNP1LE3_of_exists_tau`), which also covers infinite
characteristic-two fields; for finite fields it follows from `2 < Nat.card F`
(`nondetVPe_eq_VNP1LE3_of_natCard`, using the existing `exists_tau_of_two_lt_natCard`).
Nothing in the layer requires an `F₄` subfield or a root of `x² + x + 1`.  The reverse
containment `VNP1LE3_subset_nondetVPe` needs no characteristic hypothesis at all.

---

## G. Machine-checked here vs. external literature

### MACHINE-CHECKED HERE

* the finite compiler (existing bank) and all of section D above;
* `VP_e(F) ⊆ VNP₁^{[≤3]}(F)`;
* `N(VP_e(F)) ⊆ VNP₁^{[≤3]}(F)`;
* `VNP₁^{[≤3]}(F) ⊆ N(VP_e(F))`;
* hence the internal equality `N(VP_e(F)) = VNP₁^{[≤3]}(F)` for every characteristic-two
  field with an element `τ ∉ {0,1}`.

All of these are statements about the internal classes `VPe`, `VNP1LE3`, `VNP1`,
`NondetClosure` defined in this project.

### IMPORTED LITERATURE CONSEQUENCE (stated, never axiomatized)

1. Valiant: `VNP_e = VNP`.
2. Bringmann–Ikenmeyer–Zuiddam: `VNP₁ = VNP` for `char(F) ≠ 2`; `VNP₁ ⊊ VNP` over `F₂`;
   the remaining characteristic-two fields were left open.
3. Consequently, *if* the internal classes of this project are identified with the standard
   ones under the standard p-family definitions, the machine-checked bridge above supplies
   the missing characteristic-two, `|F| > 2` direction and externally yields
   `VNP₁(F) = VNP(F)` for every characteristic-two field `F` with more than two elements,
   completing the classification `VNP₁(F) = VNP(F) ⟺ F ≇ F₂`.

Step 3 is an external synthesis.  It is **not** a Lean theorem of this project, and no
axiom encoding steps 1–2 is declared anywhere.  This is a statement about what the formal
theorem proves; no novelty claim is made.

---

## H. Build result

```text
$ lake build
Build completed successfully (8053 jobs).
errors: none
```

(The build emits only Mathlib-style linter warnings — unused section variables and unused
simp arguments — in pre-existing files; the new files emit none.)

---

## I. Axiom audit

`#print axioms` is run in `ClassLevelAudit.lean` on every principal theorem of the new
layer.  Output for all of

```text
nondetVPe_subset_VNP1LE3        VPe_subset_VNP1LE3
VNP1LE3_subset_nondetVPe        nondetVPe_eq_VNP1LE3
nondetVPe_subset_VNP1           nondetVPe_eq_VNP1LE3_of_exists_tau
nondetVPe_eq_VNP1LE3_of_natCard ringEquiv_zmod_two_of_card_eq_two
subset_nondetClosure            AffineHypercubeRep.aeval_value
AffineHypercubeRep.reindex_value AffineForm.toFormula_eval
Formula.prodList_eval           sampleFamily_mem_VNP1LE3
```

is

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No project-specific axiom is declared.

---

## J. Placeholder audit

Search of the five new files for
`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `@[implemented_by]`:

* `sorry` / `admit` / `native_decide` / `unsafe` / `opaque` / `@[implemented_by]`:
  **no occurrences at all**;
* `axiom`: 4 occurrences, all inside documentation comments stating that nothing is
  axiomatized.

**PLACEHOLDER AUDIT: PASS.**

---

## K. Firewall

The class-level layer is a statement about *representations*: membership in `VNP1LE3`
asserts the existence, for each `n`, of a finite list of affine factors and a finite
Boolean cube whose sum of products equals `f_n` (see the marker theorem
`classLevel_scope_is_representation_only`).  It supplies **no evaluator** of a hypercube
sum, and therefore implies nothing about `P` vs `NP`, `VP` vs `VNP`, CircuitSAT, or any
runtime question.  Support-two remains OPEN and is not attempted.
