/-
# Field scope of the construction

The central algebraic theorem takes the element `τ` as an explicit hypothesis, so it covers
*infinite* characteristic-two fields as well.  For a finite field it is enough to know that
the field has more than two elements: then some `τ ∉ {0, 1}` exists.

The construction never requires a root of `x² + x + 1`, i.e. it never requires an `F₄`
subfield; `GaloisField 2 3` (the field with eight elements) is a characteristic-two field
with more than two elements in which `x² + x + 1` has no root at all, and the compiler
applies to it verbatim.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.MainCompiler

namespace VNP1Char2

open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- **Field existence corollary.**  A field with more than two elements contains an element
different from `0` and `1`. -/
theorem exists_tau_of_two_lt_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h : 2 < Fintype.card F) : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1 := by
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro x _
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · simp [hc x hx0]
  have := Finset.card_le_card hsub
  have hcard : ({0, 1} : Finset F).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  rw [Finset.card_univ] at this
  omega

/-- **The compiler over a finite characteristic-two field with more than two elements.** -/
theorem Formula.has_supportThree_representation_of_card_gt_two {ι F : Type} [Field F]
    [CharP F 2] [Fintype F] [DecidableEq F] (hF : 2 < Fintype.card F) (f : Formula ι F) :
    ∃ R : AffineHypercubeRep ι F,
      R.Represents f.eval ∧ R.SupportLE 3 ∧
        R.numAux ≤ 44 * f.size ∧ R.numFactors ≤ 84 * f.size := by
  obtain ⟨τ, hτ0, hτ1⟩ := exists_tau_of_two_lt_card hF
  exact f.has_supportThree_affineHypercubeRepresentation hτ0 hτ1

/-- **Field existence corollary, `Nat.card` form.**  A finite field with more than two
elements contains an element different from `0` and `1`. -/
theorem exists_tau_of_two_lt_natCard {F : Type*} [Field F] [Finite F]
    (h : 2 < Nat.card F) : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at h
  exact exists_tau_of_two_lt_card h

/-- **The compiler over a finite characteristic-two field with more than two elements**,
stated with `Nat.card` so that no `Fintype`/`DecidableEq` instance has to be supplied. -/
theorem Formula.has_supportThree_representation_of_natCard_gt_two {ι F : Type} [Field F]
    [CharP F 2] [Finite F] (hF : 2 < Nat.card F) (f : Formula ι F) :
    ∃ R : AffineHypercubeRep ι F,
      R.Represents f.eval ∧ R.SupportLE 3 ∧
        R.numAux ≤ 44 * f.size ∧ R.numFactors ≤ 84 * f.size := by
  obtain ⟨τ, hτ0, hτ1⟩ := exists_tau_of_two_lt_natCard hF
  exact f.has_supportThree_affineHypercubeRepresentation hτ0 hτ1

/-! ### No `F₄` subfield is needed -/

/-- In the field with eight elements the polynomial `x² + x + 1` has **no** root: `GF(8)`
contains no copy of `F₄`.  The compiler nevertheless applies to `GF(8)`, which shows that
the construction really only uses `char F = 2`, `τ ≠ 0` and `τ ≠ 1`. -/
theorem no_root_of_cyclotomic_three_GF8 (τ : GaloisField 2 3) : τ ^ 2 + τ + 1 ≠ 0 := by
  intro hτ
  have h2 : (2 : GaloisField 2 3) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 3) 2
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h] at hτ
    simp at hτ
  have hcube : τ ^ 3 = 1 := by
    linear_combination (τ + 1) * hτ - (τ ^ 2 + τ + 1) * h2
  have hcard : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  have h7 : τ ^ 7 = 1 := by
    classical
    have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
    have hc : Fintype.card (GaloisField 2 3) = 8 := by
      rwa [Nat.card_eq_fintype_card] at hcard
    have h := FiniteField.pow_card_sub_one_eq_one τ hτ0
    rwa [hc] at h
  have hone : τ = 1 := by
    have h : τ ^ 7 = (τ ^ 3) ^ 2 * τ := by ring
    rw [h7, hcube, one_pow, one_mul] at h
    exact h.symm
  rw [hone] at hτ
  have h1 : (1 : GaloisField 2 3) = 0 := by linear_combination hτ - h2
  exact one_ne_zero h1

/-- `GF(8)` is a characteristic-two field with more than two elements. -/
theorem card_GF8_gt_two : 2 < Nat.card (GaloisField 2 3) := by
  rw [GaloisField.card 2 3 (by norm_num)]
  norm_num

/-- `GF(4)` is a characteristic-two field with more than two elements. -/
theorem card_GF4_gt_two : 2 < Nat.card (GaloisField 2 2) := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

/-- `GF(16)` is a characteristic-two field with more than two elements. -/
theorem card_GF16_gt_two : 2 < Nat.card (GaloisField 2 4) := by
  rw [GaloisField.card 2 4 (by norm_num)]
  norm_num

/-- The compiler applies verbatim over `GF(8)`, a characteristic-two field containing no
copy of `F₄`. -/
theorem Formula.has_supportThree_representation_GF8 {ι : Type}
    (f : Formula ι (GaloisField 2 3)) :
    ∃ R : AffineHypercubeRep ι (GaloisField 2 3),
      R.Represents f.eval ∧ R.SupportLE 3 ∧
        R.numAux ≤ 44 * f.size ∧ R.numFactors ≤ 84 * f.size :=
  f.has_supportThree_representation_of_natCard_gt_two card_GF8_gt_two

end VNP1Char2
