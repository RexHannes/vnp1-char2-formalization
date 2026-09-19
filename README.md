# VNP₁ in characteristic two — Lean formalization

**Status: public research formalization.** This repository machine-checks an
internal class bridge for VNP₁-style affine-product representations over
characteristic-two fields with an element `τ ≠ 0, 1`.

The principal internal result is now `N(VP_e(F)) = VNP₁^[≤2](F)` for the
project’s definitions. The repository contains two machine-checked support-two
compilers: a graph/path construction and an independent direct formula-tree
construction. It also verifies polynomial total-degree coverage and a bridge from
the internal support-two class to a literal BIZ `w+`-shaped class.

## Scope

The identification of these internal classes with the standard literature classes
is an external mathematical synthesis. It is described in the reports and is not
formalized or introduced as an axiom. The project makes no claim about `P` versus
`NP`, `VP` versus `VNP`, runtime improvements, or publication novelty. The
formal result is a representation theorem and supplies no hypercube evaluator.

Start with:

- [Final bridge-repair report](VNP1_CHAR2_FINAL_BRIDGE_REPAIR_REPORT.md)
- [Support-two compiler report](VNP1_CHAR2_SUPPORT_TWO_REPORT.md)
- [Independent direct compiler report](VNP1_CHAR2_DIRECT_FORMULA_REPORT.md)
- [Original class-level report](VNP1_CHAR2_CLASS_LEVEL_REPORT.md)
- [Finite compiler and recovery report](VNP1_CHAR2_ARISTOTLE_FORMALIZATION_REPORT.md)
- [Class-level Lean aggregator](RequestProject/AlgebraicComplexity/VNP1Char2.lean)
- [Final bridge audit](RequestProject/AlgebraicComplexity/VNP1Char2/BridgeRepairAudit.lean)

## Build

The project pins Lean 4.28.0 and Mathlib v4.28.0. From the repository root:

```sh
lake build
```

The supplied reports record successful Aristotle builds, including a final
whole-project build of 8,075 jobs. This publication upload did not rerun Lean
locally because `lake` was unavailable.

## Provenance and assistance

Imported from `8f441bac-4d0c-45c5-8822-3d3f2557f429-aristotle (2).tar.gz`.
Archive SHA-256:
`2aa45567498cf49f6a6125d27016c786c37ddb02910d99ef2bf801ef5899cf70`.

Support-two, direct-compiler, and bridge-repair updates imported from
`8f441bac-4d0c-45c5-8822-3d3f2557f429-aristotle (6).tar.gz`.
Archive SHA-256:
`b79022201319f6db84b3e42b94f5853150f5aebe2ed39f07ca3518879c661bcb`.

The project used Aristotle and LLM-assisted mathematical research. Public claims
should be read at the scope stated above and in the reports.
