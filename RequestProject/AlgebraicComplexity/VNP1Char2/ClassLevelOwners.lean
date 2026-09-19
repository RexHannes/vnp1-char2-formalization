/-
# Status of the class-level layer (append-only update of `OpenOwners`)

`OpenOwners.lean` is left untouched; this file records the status of the items it listed
as open, after the class-level layer.  Nothing here is an axiom.

## BANKED (machine-checked, characteristic two, `τ ≠ 0`, `τ ≠ 1`)

* `FINITE COMPILER` — unchanged:
  `VNP1Char2.Formula.has_supportThree_affineHypercubeRepresentation`.
* `CLASS_LEVEL_VP_e_TO_VNP1` — **closed** by `VNP1Char2.VPe_subset_VNP1LE3`
  (`VP_e(F) ⊆ VNP₁^{[≤3]}(F)`).
* `N(VP_e) ⊆ VNP₁^{[≤3]}` — `VNP1Char2.nondetVPe_subset_VNP1LE3`.
* `VNP₁^{[≤3]} ⊆ N(VP_e)` — `VNP1Char2.VNP1LE3_subset_nondetVPe`.
* `INTERNAL FORMULA-VNP = VNP₁^{[≤3]}` — `VNP1Char2.nondetVPe_eq_VNP1LE3`,
  with the field forms `VNP1Char2.nondetVPe_eq_VNP1LE3_of_exists_tau` and
  `VNP1Char2.nondetVPe_eq_VNP1LE3_of_natCard`.
* `UNRESTRICTED VNP₁` — `VNP1Char2.nondetVPe_subset_VNP1`.

## NOT FORMALIZED (and not assumed anywhere)

* `STANDARD VNP IDENTIFICATION` — the classes `VNP`, `VNP₁` of the literature and
  Valiant's theorem `VNP_e = VNP` are *not* formalized here.  `VNP1Char2.VNPe` is an
  internal definition (`NondetClosure VPe`) and no theorem of this project identifies it
  with the literature class `VNP`.
* `FULL_VNP1_CLASSIFICATION` — `VNP₁(F) = VNP(F) ↔ F ≇ F₂` remains an external
  literature consequence; see the report.
* `SUPPORT_TWO` — OPEN.  No support-two upgrade is attempted; the characteristic ≠ 2
  support-two theorem of the literature uses different identities.
* `NOVELTY` — not a mathematical statement and deliberately not a Lean theorem.

## SCOPE-DEAD

The class-level layer is a *representation* statement about hypercube sums; it supplies no
evaluator.  It implies nothing about `P` versus `NP`, about `VP` versus `VNP`, and no
runtime consequence of any kind.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevelAudit

namespace VNP1Char2

/-- Marker: the class-level statement is an inclusion between representation classes, with
no computational content attached.  Membership in `VNP1LE3` asserts only the existence, for
each `n`, of a finite list of affine factors and a finite Boolean cube. -/
theorem classLevel_scope_is_representation_only {F : Type} [Field F] [CharP F 2] {τ : F}
    (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) {f : PolyFamily F} (hf : NondetClosure VPe f) :
    ∃ R : ∀ n, AffineHypercubeRep (Fin (f.nvars n)) F, ∀ n, (R n).value = f.poly n := by
  obtain ⟨hv, R, q, M, hq, hM, h⟩ := nondetVPe_subset_VNP1LE3 hτ0 hτ1 hf
  exact ⟨R, fun n => (h n).1⟩

end VNP1Char2
