# VNP₁ in characteristic two — Lean formalization

**Status: public research formalization.** This repository machine-checks an
internal class bridge for VNP₁-style affine-product representations over
characteristic-two fields with an element `τ ≠ 0, 1`.

The principal internal result is `N(VP_e(F)) = VNP₁^[≤3](F)` for the project’s
definitions. The finite compiler,
support-three representation, polynomial bounds, field corollaries, and axiom
audits are formalized in Lean.

## Scope

The identification of these internal classes with the standard literature classes
is an external mathematical synthesis. It is described in the reports and is not
formalized or introduced as an axiom. The project makes no claim about `P` versus
`NP`, `VP` versus `VNP`, runtime improvements, or publication novelty. The
support-two case remains open.

Start with:

- [Class-level report](VNP1_CHAR2_CLASS_LEVEL_REPORT.md)
- [Finite compiler and recovery report](VNP1_CHAR2_ARISTOTLE_FORMALIZATION_REPORT.md)
- [Class-level Lean aggregator](RequestProject/AlgebraicComplexity/VNP1Char2.lean)
- [Axiom audit](RequestProject/AlgebraicComplexity/VNP1Char2/ClassLevelAudit.lean)

## Build

The project pins Lean 4.28.0 and Mathlib v4.28.0. From the repository root:

```sh
lake build
```

The supplied reports record a successful Aristotle build. This publication upload
did not rerun Lean locally because `lake` was unavailable.

## Provenance and assistance

Imported from `8f441bac-4d0c-45c5-8822-3d3f2557f429-aristotle (2).tar.gz`.
Archive SHA-256:
`2aa45567498cf49f6a6125d27016c786c37ddb02910d99ef2bf801ef5899cf70`.

The project used Aristotle and LLM-assisted mathematical research. Public claims
should be read at the scope stated above and in the reports.
