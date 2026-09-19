/-
# The four-factor characteristic-two identity

Let `R` be a commutative ring of characteristic two, `τ : R`, and put

```
c  = τ³ + τ² + τ
Δ  = τ⁴ (τ+1)²
L  = b + τ e
M  = b + (τ+1) e
```

The central identity is, for Boolean `b, e` and *arbitrary* ring elements `x, y`:

```
∑_{b,e ∈ {0,1}} (x+L)(x+τL+c)(τ⁴y+M)(τ⁴y+τM+c) = Δ (1 + x y).          (ID')
```

This is a genuine identity of polynomials in `x, y` (indeed in `τ, x, y`): the proof below
is a ring computation in `R`, and `x` and `y` are universally quantified elements of an
arbitrary commutative ring of characteristic two.  In particular no relation such as
`x² = x` is used, and the identity holds verbatim after substituting the indeterminates
of a polynomial ring (see `fourFactorSum_mvPolynomial`).

Dividing by `Δ`, which is legal exactly when `τ ≠ 0` and `τ ≠ 1` over a field, yields

```
∑_{b,e ∈ {0,1}} J τ x y b e = 1 + x y.                                  (ID)
```
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.BasicBoolean

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial

section Ring

variable {R : Type*} [CommRing R]

/-- The constant `c = τ³ + τ² + τ`. -/
def cVal (τ : R) : R := τ ^ 3 + τ ^ 2 + τ

/-- The discriminant-like denominator `Δ = τ⁴ (τ+1)²`. -/
def deltaVal (τ : R) : R := τ ^ 4 * (τ + 1) ^ 2

/-- The affine form `L = b + τ e` in the two Boolean auxiliaries. -/
def LVal (τ b e : R) : R := b + τ * e

/-- The affine form `M = b + (τ+1) e` in the two Boolean auxiliaries. -/
def MVal (τ b e : R) : R := b + (τ + 1) * e

/-- The denominator-free four-factor body
`(x+L)(x+τL+c)(τ⁴y+M)(τ⁴y+τM+c)`. -/
def fourFactorBody (τ x y b e : R) : R :=
  (x + LVal τ b e) * (x + τ * LVal τ b e + cVal τ) *
    ((τ ^ 4 * y + MVal τ b e) * (τ ^ 4 * y + τ * MVal τ b e + cVal τ))

/-- **(ID')** The denominator-free four-factor identity, over any commutative ring in
which `2 = 0`.  Only `b` and `e` are Boolean; `x` and `y` are arbitrary. -/
theorem fourFactor_identity_denominator_free (h2 : (2 : R) = 0) (τ x y : R) :
    (∑ b : Bool, ∑ e : Bool, fourFactorBody τ x y (boolVal b) (boolVal e))
      = deltaVal τ * (1 + x * y) := by
  simp only [Fintype.sum_bool, fourFactorBody, cVal, deltaVal, LVal, MVal, boolVal]
  linear_combination ((4:R)*τ*x + (5:R)*τ*x^2 + (8:R)*τ^2 + (17:R)*τ^2*x + (6:R)*τ^2*x^2 +
    (22:R)*τ^3 + (27:R)*τ^3*x + (4:R)*τ^3*x^2 + (33:R)*τ^4 + (27:R)*τ^4*x + τ^4*x*y + τ^4*x^2 +
    (2:R)*τ^4*x^2*y + (29:R)*τ^5 + (3:R)*τ^5*y + (16:R)*τ^5*x + (7:R)*τ^5*x*y + (5:R)*τ^5*x^2*y +
    (17:R)*τ^6 + (11:R)*τ^6*y + (6:R)*τ^6*x + (16:R)*τ^6*x*y + (3:R)*τ^6*x^2*y + (6:R)*τ^7 +
    (18:R)*τ^7*y + τ^7*x + (18:R)*τ^7*x*y + (2:R)*τ^7*x^2*y + τ^8 + (19:R)*τ^8*y +
    (14:R)*τ^8*x*y + τ^8*x*y^2 + (2:R)*τ^8*x^2*y^2 + (12:R)*τ^9*y + (2:R)*τ^9*y^2 +
    (6:R)*τ^9*x*y + (4:R)*τ^9*x*y^2 + (5:R)*τ^10*y + (3:R)*τ^10*y^2 + (2:R)*τ^10*x*y +
    (3:R)*τ^10*x*y^2 + τ^11*y + (3:R)*τ^11*y^2 + (2:R)*τ^11*x*y^2 + τ^12*y^2) * h2

/-- Characteristic-two restatement of `(ID')`. -/
theorem fourFactor_identity_denominator_free' [CharP R 2] (τ x y : R) :
    (∑ b : Bool, ∑ e : Bool, fourFactorBody τ x y (boolVal b) (boolVal e))
      = deltaVal τ * (1 + x * y) :=
  fourFactor_identity_denominator_free (by exact_mod_cast CharP.cast_eq_zero R 2) τ x y

end Ring

section Field

variable {F : Type*} [Field F]

/-- **The denominator is legal.**  Over a field, `τ ≠ 0` and `τ ≠ 1` (and characteristic
two, so that `τ + 1 = τ - 1`) imply `Δ = τ⁴(τ+1)² ≠ 0`. -/
theorem delta_ne_zero [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    deltaVal τ ≠ 0 := by
  have h1 : τ + 1 ≠ 0 := by
    intro h
    exact hτ1 (by rw [add_eq_zero_iff_eq_neg.mp h, CharTwo.neg_eq])
  exact mul_ne_zero (pow_ne_zero _ hτ0) (pow_ne_zero _ h1)

/-- `τ = 0` makes the denominator illegal. -/
theorem delta_eq_zero_of_eq_zero : deltaVal (0 : F) = 0 := by simp [deltaVal]

/-- `τ = 1` makes the denominator illegal, in characteristic two. -/
theorem delta_eq_zero_of_eq_one [CharP F 2] : deltaVal (1 : F) = 0 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  simp only [deltaVal, one_pow, one_mul]
  rw [show (1 : F) + 1 = 2 by ring, h2]
  ring

end Field

section Algebra

variable {F : Type*} [Field F] [CharP F 2] {R : Type*} [CommRing R] [Algebra F R]

/-- In any commutative algebra over a characteristic-two field, `2 = 0`. -/
theorem two_eq_zero_of_algebra (F : Type*) [Field F] [CharP F 2] {R : Type*} [CommRing R]
    [Algebra F R] : (2 : R) = 0 := by
  have : algebraMap F R (2 : F) = (2 : R) := map_ofNat (algebraMap F R) 2
  rw [← this, show (2 : F) = 0 from by exact_mod_cast CharP.cast_eq_zero F 2, map_zero]

/-- The four-factor gadget body, with the legal denominator `Δ⁻¹` taken in the base field.
`x` and `y` are arbitrary elements of the algebra; `b` and `e` are the Boolean auxiliaries. -/
noncomputable def gadgetBody (τ : F) (x y b e : R) : R :=
  algebraMap F R (deltaVal τ)⁻¹ * fourFactorBody (algebraMap F R τ) x y b e

/-- **(ID)** The four-factor identity with denominator: over a characteristic-two field
with `τ ≠ 0, 1`, and for arbitrary elements `x y` of any commutative `F`-algebra,
`∑_{b,e ∈ {0,1}} J_τ(x,y;b,e) = 1 + x y`. -/
theorem fourFactor_identity {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (x y : R) :
    (∑ b : Bool, ∑ e : Bool, gadgetBody τ x y (boolVal b) (boolVal e)) = 1 + x * y := by
  have hΔ : deltaVal τ ≠ 0 := delta_ne_zero hτ0 hτ1
  have hmap : deltaVal (algebraMap F R τ) = algebraMap F R (deltaVal τ) := by
    simp [deltaVal, map_mul, map_pow, map_add, map_one]
  have key := fourFactor_identity_denominator_free (two_eq_zero_of_algebra F (R := R))
    (algebraMap F R τ) x y
  calc (∑ b : Bool, ∑ e : Bool, gadgetBody τ x y (boolVal b) (boolVal e))
      = algebraMap F R (deltaVal τ)⁻¹ *
          ∑ b : Bool, ∑ e : Bool, fourFactorBody (algebraMap F R τ) x y (boolVal b) (boolVal e) := by
        simp only [gadgetBody, Finset.mul_sum]
    _ = 1 + x * y := by
        rw [key, hmap, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hΔ, map_one, one_mul]

end Algebra

section MvPoly

variable {F : Type*} [Field F] [CharP F 2]

/-- **(ID) as a formal polynomial identity.**  In `MvPolynomial (Fin 2) F`, with `X = X 0`
and `Y = X 1` the two indeterminates, the four-factor sum equals `1 + X*Y`.

Note that this is an identity of formal polynomials: no Boolean or finite-field relation
on `X`, `Y` is used anywhere.  Only the two auxiliaries `b, e` range over `{0,1}`. -/
theorem fourFactorSum_mvPolynomial {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (∑ b : Bool, ∑ e : Bool,
        gadgetBody τ (X 0 : MvPolynomial (Fin 2) F) (X 1) (boolVal b) (boolVal e))
      = 1 + X 0 * X 1 :=
  fourFactor_identity hτ0 hτ1 _ _

end MvPoly

end VNP1Char2
