/-
# Audit of the class-level layer

* a non-vacuity check: the classes are inhabited, and the class theorem applies to a
  concrete family;
* `#print axioms` for every principal theorem of the class-level layer.  The expected (and
  observed) output is the standard Mathlib foundation `propext`, `Classical.choice`,
  `Quot.sound`.  No project-specific axiom is declared anywhere in this layer.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevel

namespace VNP1Char2

open MvPolynomial

variable {F : Type} [Field F]

/-! ## Non-vacuity -/

/-- A concrete family: the single variable `x₀`, in one variable for every `n`. -/
noncomputable def sampleFamily (F : Type) [Field F] : PolyFamily F :=
  ⟨fun _ => 1, fun _ => X 0⟩

theorem sampleFamily_mem_VPe : VPe (sampleFamily F) :=
  ⟨polyBounded_const 1, fun _ => Formula.var (⟨0, Nat.zero_lt_one⟩ : Fin 1), fun _ => 1,
    polyBounded_const 1,
    fun _ => ⟨rfl, le_rfl⟩⟩

/-- The class theorem applies to a concrete family, so the statement is not vacuous. -/
theorem sampleFamily_mem_VNP1LE3 [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    VNP1LE3 (sampleFamily F) :=
  VPe_subset_VNP1LE3 hτ0 hτ1 sampleFamily_mem_VPe

/-! ## Axiom audit -/

-- The p-family glossary is definitional; the class theorems are the principal results.
#print axioms VNP1Char2.nondetVPe_subset_VNP1LE3
#print axioms VNP1Char2.VPe_subset_VNP1LE3
#print axioms VNP1Char2.VNP1LE3_subset_nondetVPe
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE3
#print axioms VNP1Char2.nondetVPe_subset_VNP1
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE3_of_exists_tau
#print axioms VNP1Char2.nondetVPe_eq_VNP1LE3_of_natCard
#print axioms VNP1Char2.ringEquiv_zmod_two_of_card_eq_two

-- Supporting results of the class layer.
#print axioms VNP1Char2.subset_nondetClosure
#print axioms VNP1Char2.AffineHypercubeRep.aeval_value
#print axioms VNP1Char2.AffineHypercubeRep.reindex_value
#print axioms VNP1Char2.AffineForm.toFormula_eval
#print axioms VNP1Char2.Formula.prodList_eval
#print axioms VNP1Char2.sampleFamily_mem_VNP1LE3

end VNP1Char2
