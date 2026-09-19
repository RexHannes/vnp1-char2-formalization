/-
# Local optimality of the support-two gadget (secondary)

The memo's local optimality claim for `1 + x y` over a characteristic-two field with more
than two elements is `(q_min, m_min) = (1, 3)`:

1. zero auxiliary bits are impossible;
2. with at least one auxiliary bit, two affine factors are impossible;
3. the displayed construction achieves one bit and three factors.

**What is machine-checked here.**

* Item 3 in full: `supportTwo_gadget_achieves_one_and_three` — the gadget uses exactly one
  summed Boolean auxiliary, exactly three affine factors, each of support at most two, and
  its Boolean sum is exactly `1 + x y`.
* A weakening of item 1: `zero_aux_needs_two_factors` — with no auxiliary at all, the value
  of a representation is a plain product of affine forms, and such a product needs at least
  two factors to be `1 + X₀X₁`, because `1 + X₀X₁` has total degree two while an affine
  form has total degree at most one.

**What is NOT machine-checked here** (and is therefore not claimed anywhere in this
project):

* the full form of item 1 — that *no* product of affine forms whatsoever equals `1 + X₀X₁`
  (this is the irreducibility of `1 + X₀X₁` in `F[X₀,X₁]`, which is not formalized here);
* item 2.

Neither is used by the support-two compiler; this file is a side result, exactly as the
memo prescribes.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevelTwo

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial AffineForm

variable {F : Type} [Field F]

/-- `1 + X₀X₁` has total degree two. -/
theorem totalDegree_one_add_X_mul_X :
    (1 + X 0 * X 1 : MvPolynomial (Fin 2) F).totalDegree = 2 := by
  have h1 : (X 0 * X 1 : MvPolynomial (Fin 2) F).totalDegree = 2 := by
    rw [totalDegree_mul_of_isDomain (X_ne_zero 0) (X_ne_zero 1), totalDegree_X, totalDegree_X]
  rw [totalDegree_add_eq_right_of_totalDegree_lt (by rw [h1, totalDegree_one]; norm_num), h1]

/-- **No auxiliary bit needs at least two affine factors.**  A product of at most one affine
form has total degree at most one, so it cannot be `1 + X₀X₁`. -/
theorem zero_aux_needs_two_factors (L : List (AffineForm (Fin 2) F))
    (hL : (L.map AffineForm.toPoly).prod = 1 + X 0 * X 1) : 2 ≤ L.length := by
  by_contra hlen
  push_neg at hlen
  interval_cases h : L.length
  · rw [List.length_eq_zero_iff.mp h] at hL
    simp only [List.map_nil, List.prod_nil] at hL
    have hX : (X 0 * X 1 : MvPolynomial (Fin 2) F) = 0 := by linear_combination -hL
    exact (mul_ne_zero (X_ne_zero (R := F) 0) (X_ne_zero (R := F) 1)) hX
  · obtain ⟨A, rfl⟩ := List.length_eq_one_iff.mp h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hL
    have h1 : (A.toPoly).totalDegree ≤ 1 := AffineForm.toPoly_totalDegree_le_one A
    rw [hL, totalDegree_one_add_X_mul_X] at h1
    omega

/-- **The construction achieves one auxiliary bit and three affine factors.**  Over a
characteristic-two field with `τ ≠ 0, 1`, the three affine forms of `gadget2Factors`, each
of support at most two, sum over the single Boolean auxiliary to `1 + x y`. -/
theorem supportTwo_gadget_achieves_one_and_three [CharP F 2] {τ : F} (hτ0 : τ ≠ 0)
    (hτ1 : τ ≠ 1) {σ : Type} (x y : AffineForm σ F) (hx : x.numVars ≤ 1) (hy : y.numVars ≤ 1)
    (hIdx : σ) {M : Type} [CommRing M] [Algebra F M] (g : Bool → σ → M)
    (hh : ∀ h, g h hIdx = boolVal h)
    (hxg : ∀ h, x.eval (g h) = x.eval (g false)) (hyg : ∀ h, y.eval (g h) = y.eval (g false)) :
    (gadget2Factors τ x y hIdx).length = 3 ∧
      (∀ A ∈ gadget2Factors τ x y hIdx, A.numVars ≤ 2) ∧
      (∑ h : Bool, ((gadget2Factors τ x y hIdx).map fun A => A.eval (g h)).prod)
        = 1 + x.eval (g false) * y.eval (g false) := by
  refine ⟨length_gadget2Factors .., fun A hA => ?_,
    sum_prod_gadget2Factors hτ0 hτ1 x y hIdx g hh hxg hyg⟩
  have := numVars_gadget2Factors_le hA
  omega

end VNP1Char2
