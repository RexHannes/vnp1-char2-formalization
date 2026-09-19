/-
# Audit of the final bridge repair

Append-only audit layer for the two certification bridges:

* `PFamilyDegree` — the standard p-family total-degree condition;
* `BIZWPlus` — the literal width-one `w+` support-two literature-shaped class.

It contains

* a non-vacuity check (a concrete family lands in the new `w+` class and is a standard
  p-family);
* a firewall showing that total degree at most one does *not* imply the `w+` support
  condition, so the new class `VNP1BIZWPlus` is genuinely stronger than `VNP1BIZ` and the
  bridge theorem is not a restatement;
* a field-scope note: the positive hypothesis used everywhere is `∃ τ, τ ≠ 0 ∧ τ ≠ 1`, and
  no statement of this project uses type equality or type inequality with `F₂`;
* `#print axioms` on every new principal theorem.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.BIZWPlus
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevelAudit

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial

variable {F : Type} [Field F]

/-! ## Non-vacuity -/

/-- The concrete family `x₀` is a standard p-family. -/
theorem sampleFamily_isPFamily : IsPFamily (sampleFamily F) :=
  VPe.isPFamily sampleFamily_mem_VPe

/-- The concrete family `x₀` lands in the literal `w+` class, so the bridge is not
vacuous. -/
theorem sampleFamily_mem_VNP1BIZWPlus [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    VNP1BIZWPlus (sampleFamily F) :=
  VPe_subset_VNP1BIZWPlus hτ0 hτ1 sampleFamily_mem_VPe

/-! ## Firewall: total degree ≤ 1 does not imply `w+` support ≤ 2 -/

/-- **The `w+` condition is a genuine strengthening.**  The polynomial `x₀ + x₁ + x₂` has
total degree one — so it is a legal factor for the weaker class `VNP1BIZ` — but it mentions
three variables, so it is *not* a legal factor for `VNP1BIZWPlus`.  Hence the bridge
`VNP1LE2 ⊆ VNP1BIZWPlus` really does carry support information, and the support-two claim
cannot be obtained from the degree condition alone. -/
theorem totalDegree_one_not_supportTwo :
    (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) (ZMod 2)).totalDegree ≤ 1 ∧
      ¬ ((X 0 + X 1 + X 2 : MvPolynomial (Fin 3) (ZMod 2)).vars.card ≤ 2) := by
  have hvars : (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) (ZMod 2)).vars.card = 3 := by
    have h01 : (X 0 + X 1 : MvPolynomial (Fin 3) (ZMod 2)).vars = {0, 1} := by
      rw [vars_add_of_disjoint] <;> simp [vars_X]
    have h : ((X 0 + X 1 : MvPolynomial (Fin 3) (ZMod 2)) + X 2).vars = {0, 1, 2} := by
      rw [vars_add_of_disjoint (by rw [h01]; simp [vars_X]), h01]
      simp [vars_X]
    rw [show (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) (ZMod 2)) = (X 0 + X 1) + X 2 from rfl, h]
    decide
  refine ⟨?_, by rw [hvars]; omega⟩
  refine le_trans (totalDegree_add _ _) (max_le (le_trans (totalDegree_add _ _)
    (max_le ?_ ?_)) ?_) <;> exact le_of_eq (totalDegree_X _)

/-! ## Field-scope note

The canonical positive hypothesis of the whole project is the explicit element hypothesis
`∃ τ : F, τ ≠ 0 ∧ τ ≠ 1`, which also covers infinite characteristic-two fields; the
finite-cardinality statements (`2 < Nat.card F`, `2 < Fintype.card F`) are corollaries of
it and are never used as the universal statement.  No theorem of this project states type
equality or type inequality with `F₂`: the only appearance of the two-element field is the
ring *isomorphism* statement `ringEquiv_zmod_two_of_card_eq_two`, recorded for
completeness.  The marker below records the canonical hypothesis. -/

/-- Field-scope marker: over a characteristic-two field, the canonical hypothesis
`∃ τ, τ ≠ 0 ∧ τ ≠ 1` is exactly what the class theorem consumes. -/
theorem field_scope_marker [CharP F 2] (hτ : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1) {f : PolyFamily F}
    (hf : NondetClosure VPe f) : VNP1BIZWPlus f ∧ IsPFamily f := by
  obtain ⟨τ, hτ0, hτ1⟩ := hτ
  exact ⟨nondetVPe_subset_VNP1BIZWPlus hτ0 hτ1 hf, nondetVPe_isPFamily hf⟩

/-! ## Axiom audit: the standard p-family degree layer -/

#print axioms VNP1Char2.Formula.totalDegree_eval_le
#print axioms VNP1Char2.VPe.polyDegreeBounded
#print axioms VNP1Char2.VPe.isPFamily
#print axioms VNP1Char2.AffineForm.totalDegree_eval_le_one
#print axioms VNP1Char2.AffineHypercubeRep.totalDegree_value_le
#print axioms VNP1Char2.VNP1.polyDegreeBounded
#print axioms VNP1Char2.VNP1.isPFamily
#print axioms VNP1Char2.VNP1LE3.isPFamily
#print axioms VNP1Char2.VNP1LE2.isPFamily
#print axioms VNP1Char2.totalDegree_aeval_le
#print axioms VNP1Char2.NondetClosure.polyDegreeBounded
#print axioms VNP1Char2.NondetClosure.isPFamily
#print axioms VNP1Char2.nondetVPe_isPFamily
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE2_standard
#print axioms VNP1Char2.nondetVPe_iff_VNP1LE2_isPFamily
#print axioms VNP1Char2.nondetVPe_subset_VNP1LE2_standard
#print axioms VNP1Char2.VNP1LE2_subset_nondetVPe_standard
#print axioms VNP1Char2.VPe_subset_VNP1LE2_standard

/-! ## Axiom audit: the literal `w+` bridge -/

#print axioms VNP1Char2.AffineForm.toPoly_vars_subset
#print axioms VNP1Char2.AffineForm.toPoly_vars_card_le
#print axioms VNP1Char2.VNP1BIZWPlus.toVNP1BIZ
#print axioms VNP1Char2.VNP1LE2_subset_VNP1BIZWPlus
#print axioms VNP1Char2.nondetVPe_subset_VNP1BIZWPlus
#print axioms VNP1Char2.VPe_subset_VNP1BIZWPlus
#print axioms VNP1Char2.nondetVPe_subset_VNP1BIZWPlus_standard

/-! ## Axiom audit: audit-layer statements -/

#print axioms VNP1Char2.sampleFamily_isPFamily
#print axioms VNP1Char2.sampleFamily_mem_VNP1BIZWPlus
#print axioms VNP1Char2.totalDegree_one_not_supportTwo
#print axioms VNP1Char2.field_scope_marker

end VNP1Char2
