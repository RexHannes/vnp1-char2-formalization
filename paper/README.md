# Preprint draft

## Title

**Nondeterministic Width-One Algebraic Branching Programs in Characteristic Two**

This directory contains a journal-style draft based on the append-only support-two Lean
layer recorded in `VNP1_CHAR2_SUPPORT_TWO_REPORT.md`.

## Main statements in the draft

For a field `F` of characteristic two with an element `τ ≠ 0, 1`, every binary
division-free arithmetic formula of size `s` has an affine-product Boolean-hypercube
representation in which every factor uses at most two variables, with certified bounds

```text
q ≤ 14 s,
M ≤ 34 s.
```

At the internal class level, the artifact proves

```text
N(VP_e(F)) = VNP₁^[≤2](F).
```

The passage to the standard literature notation uses external results of Valiant and
Bringmann--Ikenmeyer--Zuiddam and is kept separate from the machine-checked statements.

## Build the paper

The source is self-contained and uses a manual bibliography, so a BibTeX executable is not
required:

```sh
pdflatex main.tex
pdflatex main.tex
```

## Verification boundary

The supplied support-two report records a successful Lean 4.28.0 / Mathlib v4.28.0 build
and a clean `#print axioms` audit. The manuscript-production environment statically
inspected the archive but did not independently rerun Lean because `lake` was unavailable.
The PDF was compiled from `main.tex` and visually inspected page by page.

## Draft status

This is a research preprint draft, not a peer-reviewed publication. Author information,
acknowledgements, repository commit identifiers, and a final literature/priority audit
should be completed before public submission.
