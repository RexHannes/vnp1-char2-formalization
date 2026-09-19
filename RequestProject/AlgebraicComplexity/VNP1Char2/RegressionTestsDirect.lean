/-
# Machine-checked regression tests for the direct formula-tree compiler

All statements in this file are theorems (or `example`s), so they are checked by the build.

Covered:

1. the branch-gadget truth table for all eight `(a,b,c)` states, and the fact that exactly
   three states are allowed;
2. representative leaves (a variable leaf and a constant leaf);
3. one addition formula and 4. one multiplication formula;
5. the mixed formulas `(x + y) * z`, `x + (y * z)` and `(x + 1) * (y + z)`;
6. the compiled value equals the formula evaluation in each case;
7. support at most two;
8. exact auxiliary counts and 9. exact factor counts;
10. two equal-shaped subformulas get disjoint fresh auxiliaries (the count doubles).

Concrete finite fields `GF(4)` and `GF(16)` are covered as well.

The last section is a **scope firewall**: `(BRANCH)` is a Boolean-semantic identity only.
For a parent activation value `c ∉ {0,1}` the branch sum really differs from
`(1 + a + b + c)(1 + a b)`, so the unrestricted polynomial statement is false and is never
claimed.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.DirectFormulaCompiler
import RequestProject.AlgebraicComplexity.VNP1Char2.FieldCorollary

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial AffineForm

/-! ## 1. The branch-gadget truth table -/

/-- Exactly three of the eight Boolean states are allowed by the branch gadget. -/
example : ((Finset.univ : Finset (Bool × Bool × Bool)).filter
    fun t => BranchAllowed t.1 t.2.1 t.2.2).card = 3 := by decide

/-- The three allowed states are `(0,0,0)`, `(1,0,1)` and `(0,1,1)`: an inactive parent
forces both children inactive, an active parent activates exactly one child. -/
example : BranchAllowed false false false ∧ BranchAllowed true false true ∧
    BranchAllowed false true true ∧ ¬ BranchAllowed true true true ∧
    ¬ BranchAllowed false false true ∧ ¬ BranchAllowed true false false ∧
    ¬ BranchAllowed false true false ∧ ¬ BranchAllowed true true false := by decide

section Tests

variable {F : Type} [Field F] [CharP F 2]

/-- The truth table of the branch gadget, for all eight states. -/
theorem branch_truth_table_all {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (a b c : Bool) :
    (∑ h : Bool, branchBody τ (boolVal a) (boolVal b) (boolVal c) (boolVal h))
      = if BranchAllowed a b c then 1 else 0 :=
  branch_truth_table hτ0 hτ1 a b c

/-! ## 2.–6. Representative formulas, compiled values -/

/-- The leaf formula `x₀`. -/
def testVar : Formula (Fin 3) F := .var 0

/-- The constant leaf formula `1`. -/
def testConst : Formula (Fin 3) F := .const 1

/-- `x₀ + x₁`. -/
def testAdd : Formula (Fin 3) F := .add (.var 0) (.var 1)

/-- `x₀ * x₁`. -/
def testMul : Formula (Fin 3) F := .mul (.var 0) (.var 1)

/-- `(x₀ + x₁) * x₂`. -/
def testAddMul : Formula (Fin 3) F := .mul (.add (.var 0) (.var 1)) (.var 2)

/-- `x₀ + (x₁ * x₂)`. -/
def testMulAdd : Formula (Fin 3) F := .add (.var 0) (.mul (.var 1) (.var 2))

/-- `(x₀ + 1) * (x₁ + x₂)`. -/
def testMixed : Formula (Fin 3) F :=
  .mul (.add (.var 0) (.const 1)) (.add (.var 1) (.var 2))

/-- `(x₀ + x₁) * (x₀ + x₁)`: two equal-shaped subformulas. -/
def testDup : Formula (Fin 3) F :=
  .mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))

variable {τ : F}

theorem directRep_value_var (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (Formula.directRep τ (testVar (F := F))).value = X 0 := by
  rw [Formula.directRep_value _ hτ0 hτ1]; rfl

theorem directRep_value_const (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (Formula.directRep τ (testConst (F := F))).value = C 1 := by
  rw [Formula.directRep_value _ hτ0 hτ1]; rfl

theorem directRep_value_add (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (Formula.directRep τ (testAdd (F := F))).value = X 0 + X 1 := by
  rw [Formula.directRep_value _ hτ0 hτ1]; rfl

theorem directRep_value_mul (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (Formula.directRep τ (testMul (F := F))).value = X 0 * X 1 := by
  rw [Formula.directRep_value _ hτ0 hτ1]; rfl

theorem directRep_value_addMul (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (Formula.directRep τ (testAddMul (F := F))).value = (X 0 + X 1) * X 2 := by
  rw [Formula.directRep_value _ hτ0 hτ1]; rfl

theorem directRep_value_mulAdd (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (Formula.directRep τ (testMulAdd (F := F))).value = X 0 + X 1 * X 2 := by
  rw [Formula.directRep_value _ hτ0 hτ1]; rfl

theorem directRep_value_mixed (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (Formula.directRep τ (testMixed (F := F))).value = (X 0 + C 1) * (X 1 + X 2) := by
  rw [Formula.directRep_value _ hτ0 hτ1]; rfl

theorem directRep_value_dup (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (Formula.directRep τ (testDup (F := F))).value = (X 0 + X 1) * (X 0 + X 1) := by
  rw [Formula.directRep_value _ hτ0 hτ1]; rfl

/-! ## 7. Support at most two -/

omit [CharP F 2] in
theorem directRep_supportLE_two_mixed (τ : F) :
    (Formula.directRep τ (testMixed (F := F))).SupportLE 2 :=
  Formula.directRep_supportLE_two τ _

omit [CharP F 2] in
theorem directRep_supportLE_two_dup (τ : F) :
    (Formula.directRep τ (testDup (F := F))).SupportLE 2 :=
  Formula.directRep_supportLE_two τ _

/-! ## 8.–9. Exact auxiliary and factor counts -/

omit [CharP F 2] in
theorem directRep_counts_addMul (τ : F) :
    (Formula.directRep τ (testAddMul (F := F))).numAux = 9 ∧
      (Formula.directRep τ (testAddMul (F := F))).numFactors = 18 :=
  ⟨Formula.directRep_numAux τ _, Formula.directRep_numFactors τ _⟩

omit [CharP F 2] in
theorem directRep_counts_mulAdd (τ : F) :
    (Formula.directRep τ (testMulAdd (F := F))).numAux = 9 ∧
      (Formula.directRep τ (testMulAdd (F := F))).numFactors = 18 :=
  ⟨Formula.directRep_numAux τ _, Formula.directRep_numFactors τ _⟩

omit [CharP F 2] in
theorem directRep_counts_mixed (τ : F) :
    (Formula.directRep τ (testMixed (F := F))).numAux = 13 ∧
      (Formula.directRep τ (testMixed (F := F))).numFactors = 27 :=
  ⟨Formula.directRep_numAux τ _, Formula.directRep_numFactors τ _⟩

omit [CharP F 2] in
/-- The general bounds `q ≤ 2s` and `M ≤ 5s` on a concrete example: `s = 5`, `q = 9`,
`M = 18`. -/
theorem directRep_bounds_addMul (τ : F) :
    (Formula.directRep τ (testAddMul (F := F))).numAux ≤ 2 * (testAddMul (F := F)).size ∧
      2 * (Formula.directRep τ (testAddMul (F := F))).numFactors
        ≤ 9 * (testAddMul (F := F)).size ∧
      (Formula.directRep τ (testAddMul (F := F))).numFactors
        ≤ 5 * (testAddMul (F := F)).size :=
  ⟨Formula.directRep_numAux_le τ _, Formula.directRep_two_numFactors_le τ _,
    Formula.directRep_numFactors_le τ _⟩

/-! ## 10. Freshness: equal-shaped subformulas do not share auxiliaries -/

omit [CharP F 2] in
/-- The two equal-shaped copies of `x₀ + x₁` inside `(x₀+x₁)*(x₀+x₁)` receive **disjoint**
auxiliaries: the auxiliary count is twice that of one copy, plus the root activation bit of
the multiplication node.  Sharing would give `7` instead of `13`. -/
theorem directRep_fresh_dup (τ : F) :
    (Formula.directRep τ (testDup (F := F))).numAux
      = 2 * (Formula.directRep τ (testAdd (F := F))).numAux + 1 := by
  rw [Formula.directRep_numAux, Formula.directRep_numAux]
  rfl

omit [CharP F 2] in
theorem directRep_counts_dup (τ : F) :
    (Formula.directRep τ (testDup (F := F))).numAux = 13 ∧
      (Formula.directRep τ (testDup (F := F))).numFactors = 27 :=
  ⟨Formula.directRep_numAux τ _, Formula.directRep_numFactors τ _⟩

/-! ## Scope firewall: `(BRANCH)` is a Boolean-semantic identity only -/

/-- **The unrestricted branch identity is false.**  With both children inactive and a
parent value `c ∉ {0,1}`, the branch sum differs from `(1 + a + b + c)(1 + a b)` by
`(1 + κ⁻¹) c (c + 1) ≠ 0`, provided `κ ≠ 1`.  Hence `(BRANCH)` may only be asserted for
Boolean `a, b, c`, which is exactly how it is stated and used. -/
theorem branch_unrestricted_fails {c : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    (hκ : kappaVal τ ≠ 1) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (∑ h : Bool, branchBody τ 0 0 c (boolVal h)) ≠ (1 + 0 + 0 + c) * (1 + 0 * 0) := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hκ0 : kappaVal τ ≠ 0 := kappa_ne_zero hτ0 hτ1
  have hv : τ + 1 ≠ 0 := fun h => hτ1 (by rw [add_eq_zero_iff_eq_neg.mp h, CharTwo.neg_eq])
  have hkey : (∑ h : Bool, branchBody τ 0 0 c (boolVal h)) - (1 + 0 + 0 + c) * (1 + 0 * 0)
      = (1 + (kappaVal τ)⁻¹) * (c * (c + 1)) := by
    have hinv : (kappaVal τ)⁻¹ * kappaVal τ = 1 := inv_mul_cancel₀ hκ0
    simp only [Fintype.sum_bool, branchBody, boolVal, kappaVal] at *
    field_simp
    ring_nf
    linear_combination (c ^ 2 * τ ^ 2 + c ^ 2 * τ + c * τ ^ 2 + c * τ + τ ^ 3 + 2 * τ ^ 2 + τ
      + 4 * τ * c + 2 * τ * c ^ 2 + 2 * τ ^ 2 + 10 * τ ^ 2 * c + 4 * τ ^ 2 * c ^ 2 + 7 * τ ^ 3
      + 13 * τ ^ 3 * c + 4 * τ ^ 3 * c ^ 2 + 9 * τ ^ 4 + 8 * τ ^ 4 * c + τ ^ 4 * c ^ 2
      + 5 * τ ^ 5 + 2 * τ ^ 5 * c + τ ^ 6 + c + c ^ 2) * h2
  intro hEq
  rw [hEq, sub_self] at hkey
  have h1 : (1 : F) + (kappaVal τ)⁻¹ ≠ 0 := by
    intro h
    apply hκ
    have : (kappaVal τ)⁻¹ = 1 := by
      have := add_eq_zero_iff_eq_neg.mp h
      rw [this, CharTwo.neg_eq]
    field_simp at this
    exact this.symm
  have hc : c * (c + 1) ≠ 0 := by
    refine mul_ne_zero hc0 fun h => hc1 ?_
    rw [add_eq_zero_iff_eq_neg.mp h, CharTwo.neg_eq]
  exact (mul_ne_zero h1 hc) hkey.symm

end Tests

/-! ## Concrete characteristic-two fields -/

/-- The direct compiler applies verbatim over `GF(4)`. -/
theorem Formula.has_supportTwo_representation_direct_GF4 {ι : Type}
    (f : Formula ι (GaloisField 2 2)) :
    ∃ R : AffineHypercubeRep ι (GaloisField 2 2),
      R.Represents f.eval ∧ R.SupportLE 2 ∧ R.numAux ≤ 2 * f.size ∧
        2 * R.numFactors ≤ 9 * f.size ∧ R.numFactors ≤ 5 * f.size :=
  f.has_supportTwo_representation_direct_of_exists_tau
    (exists_tau_of_two_lt_natCard card_GF4_gt_two)

/-- The direct compiler applies verbatim over `GF(16)`. -/
theorem Formula.has_supportTwo_representation_direct_GF16 {ι : Type}
    (f : Formula ι (GaloisField 2 4)) :
    ∃ R : AffineHypercubeRep ι (GaloisField 2 4),
      R.Represents f.eval ∧ R.SupportLE 2 ∧ R.numAux ≤ 2 * f.size ∧
        2 * R.numFactors ≤ 9 * f.size ∧ R.numFactors ≤ 5 * f.size :=
  f.has_supportTwo_representation_direct_of_exists_tau
    (exists_tau_of_two_lt_natCard card_GF16_gt_two)

/-- The direct compiler applies verbatim over `GF(8)`, which contains **no** copy of `F₄`:
the construction uses only `char F = 2`, `τ ≠ 0` and `τ ≠ 1`. -/
theorem Formula.has_supportTwo_representation_direct_GF8 {ι : Type}
    (f : Formula ι (GaloisField 2 3)) :
    ∃ R : AffineHypercubeRep ι (GaloisField 2 3),
      R.Represents f.eval ∧ R.SupportLE 2 ∧ R.numAux ≤ 2 * f.size ∧
        2 * R.numFactors ≤ 9 * f.size ∧ R.numFactors ≤ 5 * f.size :=
  f.has_supportTwo_representation_direct_of_exists_tau
    (exists_tau_of_two_lt_natCard card_GF8_gt_two)

end VNP1Char2
