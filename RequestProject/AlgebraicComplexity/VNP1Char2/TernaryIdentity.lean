/-
# The support-two characteristic-two identities

This is a new, strictly append-only layer.  Nothing in the existing support-three files is
modified, renamed, weakened or reproved.

Let `R` be a commutative ring of characteristic two, `τ : R`, and put

```
κ = τ (τ + 1).
```

Two identities are proved here, both as ring identities in which **only the auxiliary `h`
is Boolean**; all the other letters are arbitrary ring elements, so the identities hold
verbatim after substituting indeterminates of a polynomial ring (see the `MvPoly` section).

* the **support-two `1 + x y` gadget** (one Boolean auxiliary, three factors)

```
∑_{h ∈ {0,1}} (τ + 1 + h) (x + τ + h) (κ y + τ + h) = κ (1 + x y);          (ID2')
```

* the **ternary flow gadget** (one Boolean auxiliary, four factors)

```
∑_{h ∈ {0,1}} (τ + 1 + h)(a + τ + h)(b + τ + h)(c + τ + h)
    = κ (1 + a + b + c) + a b c.                                           (ID3')
```

Dividing by `κ`, which is legal exactly when `τ ≠ 0` and `τ ≠ 1` over a field, yields the
gadget bodies `twoGadgetBody` and `ternGadgetBody` used by the compiler.

**Proof-order firewall.**  `(ID3')` carries the *cubic error* `a b c`, which is **not**
zero as a formal polynomial, and `a b c (1 + a b) = 0` is **not** a formal polynomial
identity either.  The error is killed only pointwise, after the selector variables have
been evaluated on a Boolean assignment and against a same-head/same-tail exclusion factor;
see `boolVal_mul_mul_one_add_mul` below and `CompilerTwo.lean`.  No file in this layer ever
rewrites `a b c (1 + a b) = 0` inside an unrestricted polynomial ring.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.FourFactorIdentity

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial

section Ring

variable {R : Type*} [CommRing R]

/-- The support-two denominator `κ = τ (τ + 1)`. -/
def kappaVal (τ : R) : R := τ * (τ + 1)

/-- The denominator-free support-two body `(τ+1+h)(x+τ+h)(κ y+τ+h)`. -/
def twoFactorBody (τ x y h : R) : R :=
  (τ + 1 + h) * (x + τ + h) * (kappaVal τ * y + τ + h)

/-- **(ID2')** The denominator-free support-two identity, over any commutative ring in
which `2 = 0`.  Only `h` is Boolean; `x` and `y` are arbitrary. -/
theorem twoFactor_identity_denominator_free (h2 : (2 : R) = 0) (τ x y : R) :
    (∑ h : Bool, twoFactorBody τ x y (boolVal h)) = kappaVal τ * (1 + x * y) := by
  simp only [Fintype.sum_bool, twoFactorBody, kappaVal, boolVal]
  linear_combination (τ * (τ * (τ + 1)) * x * y + τ * (τ + 1) * x * y + τ ^ 2 * x + 2 * τ * x + x
    + τ * (τ + 1) * τ ^ 2 * y + 2 * (τ * (τ + 1)) * τ * y + τ * (τ + 1) * y
    + τ ^ 3 + 2 * τ ^ 2 + 2 * τ + 1) * h2

/-- The denominator-free ternary body `(τ+1+h)(a+τ+h)(b+τ+h)(c+τ+h)`. -/
def ternFactorBody (τ a b c h : R) : R :=
  (τ + 1 + h) * (a + τ + h) * ((b + τ + h) * (c + τ + h))

/-- **(ID3')** The denominator-free ternary identity, over any commutative ring in which
`2 = 0`.  Only `h` is Boolean; `a`, `b`, `c` are arbitrary.  Note the cubic error `a b c`:
it is a genuine term of the formal polynomial identity and is *not* discarded here. -/
theorem ternFactor_identity_denominator_free (h2 : (2 : R) = 0) (τ a b c : R) :
    (∑ h : Bool, ternFactorBody τ a b c (boolVal h))
      = kappaVal τ * (1 + a + b + c) + a * b * c := by
  simp only [Fintype.sum_bool, ternFactorBody, kappaVal, boolVal]
  linear_combination ((τ + 1) * (a * b * c) + (τ ^ 2 + 2 * τ + 1) * (a * b + a * c + b * c)
    + (τ ^ 3 + 2 * τ ^ 2 + 2 * τ + 1) * (a + b + c)
    + (τ ^ 4 + 3 * τ ^ 3 + 4 * τ ^ 2 + 3 * τ + 1)) * h2

/-- **The pointwise cubic-error killer.**  For Boolean values `u`, `v`, `w` of a ring of
characteristic two, `u v w (1 + u v) = 0`.  This is the *only* place where Booleanness of
the selector variables is used, and it is used pointwise, never as a polynomial rewrite. -/
theorem boolVal_mul_mul_one_add_mul (h2 : (2 : R) = 0) (u v w : Bool) :
    (boolVal u : R) * boolVal v * boolVal w * (1 + boolVal u * boolVal v) = 0 := by
  have hsq : (boolVal u : R) * boolVal v * boolVal w * (boolVal u * boolVal v)
      = boolVal u * boolVal v * boolVal w := by
    have hu := boolVal_mul_self (R := R) u
    have hv := boolVal_mul_self (R := R) v
    calc (boolVal u : R) * boolVal v * boolVal w * (boolVal u * boolVal v)
        = (boolVal u * boolVal u) * (boolVal v * boolVal v) * boolVal w := by ring
      _ = boolVal u * boolVal v * boolVal w := by rw [hu, hv]
  rw [mul_add, mul_one, hsq]
  linear_combination ((boolVal u : R) * boolVal v * boolVal w) * h2

end Ring

section Field

variable {F : Type*} [Field F]

/-- **The support-two denominator is legal.**  Over a field of characteristic two,
`τ ≠ 0` and `τ ≠ 1` imply `κ = τ(τ+1) ≠ 0`. -/
theorem kappa_ne_zero [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    kappaVal τ ≠ 0 := by
  have h1 : τ + 1 ≠ 0 := by
    intro h
    exact hτ1 (by rw [add_eq_zero_iff_eq_neg.mp h, CharTwo.neg_eq])
  exact mul_ne_zero hτ0 h1

/-- `τ = 0` makes the support-two denominator illegal. -/
theorem kappa_eq_zero_of_eq_zero : kappaVal (0 : F) = 0 := by simp [kappaVal]

/-- `τ = 1` makes the support-two denominator illegal, in characteristic two. -/
theorem kappa_eq_zero_of_eq_one [CharP F 2] : kappaVal (1 : F) = 0 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  simp only [kappaVal, one_mul]
  linear_combination h2

end Field

section Algebra

variable {F : Type*} [Field F] [CharP F 2] {R : Type*} [CommRing R] [Algebra F R]

/-- The support-two gadget body, with the legal denominator `κ⁻¹` taken in the base field.
`x` and `y` are arbitrary elements of the algebra; `h` is the single Boolean auxiliary. -/
noncomputable def twoGadgetBody (τ : F) (x y h : R) : R :=
  algebraMap F R (kappaVal τ)⁻¹ * twoFactorBody (algebraMap F R τ) x y h

/-- The ternary gadget body, with the legal denominator `κ⁻¹`. -/
noncomputable def ternGadgetBody (τ : F) (a b c h : R) : R :=
  algebraMap F R (kappaVal τ)⁻¹ * ternFactorBody (algebraMap F R τ) a b c h

omit [CharP F 2] in
theorem kappaVal_algebraMap (τ : F) :
    kappaVal (algebraMap F R τ) = algebraMap F R (kappaVal τ) := by
  simp [kappaVal, map_mul, map_add, map_one]

/-- **(ID2)** The support-two identity with denominator: over a characteristic-two field
with `τ ≠ 0, 1`, and for arbitrary elements `x y` of any commutative `F`-algebra,
`∑_{h ∈ {0,1}} κ⁻¹ (τ+1+h)(x+τ+h)(κ y+τ+h) = 1 + x y`.  One auxiliary bit, three affine
factors. -/
theorem twoFactor_identity {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (x y : R) :
    (∑ h : Bool, twoGadgetBody τ x y (boolVal h)) = 1 + x * y := by
  have hκ : kappaVal τ ≠ 0 := kappa_ne_zero hτ0 hτ1
  have key := twoFactor_identity_denominator_free (two_eq_zero_of_algebra F (R := R))
    (algebraMap F R τ) x y
  calc (∑ h : Bool, twoGadgetBody τ x y (boolVal h))
      = algebraMap F R (kappaVal τ)⁻¹ *
          ∑ h : Bool, twoFactorBody (algebraMap F R τ) x y (boolVal h) := by
        simp only [twoGadgetBody, Finset.mul_sum]
    _ = 1 + x * y := by
        rw [key, kappaVal_algebraMap, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hκ, map_one,
          one_mul]

/-- **(ID3)** The ternary identity with denominator: the Boolean sum of the four-factor
ternary body is the affine flow factor `1 + a + b + c` **plus the cubic error**
`κ⁻¹ a b c`. -/
theorem ternFactor_identity {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (a b c : R) :
    (∑ h : Bool, ternGadgetBody τ a b c (boolVal h))
      = (1 + a + b + c) + algebraMap F R (kappaVal τ)⁻¹ * (a * b * c) := by
  have hκ : kappaVal τ ≠ 0 := kappa_ne_zero hτ0 hτ1
  have key := ternFactor_identity_denominator_free (two_eq_zero_of_algebra F (R := R))
    (algebraMap F R τ) a b c
  calc (∑ h : Bool, ternGadgetBody τ a b c (boolVal h))
      = algebraMap F R (kappaVal τ)⁻¹ *
          ∑ h : Bool, ternFactorBody (algebraMap F R τ) a b c (boolVal h) := by
        simp only [ternGadgetBody, Finset.mul_sum]
    _ = (1 + a + b + c) + algebraMap F R (kappaVal τ)⁻¹ * (a * b * c) := by
        rw [key, kappaVal_algebraMap, mul_add, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hκ,
          map_one, one_mul]

end Algebra

section MvPoly

variable {F : Type*} [Field F] [CharP F 2]

/-- **(ID2) as a formal polynomial identity** in `MvPolynomial (Fin 2) F`.  No Boolean or
finite-field relation on `X 0`, `X 1` is used; only `h` ranges over `{0,1}`. -/
theorem twoFactorSum_mvPolynomial {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (∑ h : Bool, twoGadgetBody τ (X 0 : MvPolynomial (Fin 2) F) (X 1) (boolVal h))
      = 1 + X 0 * X 1 :=
  twoFactor_identity hτ0 hτ1 _ _

/-- **(ID3) as a formal polynomial identity** in `MvPolynomial (Fin 3) F`.  The cubic error
term is visibly present: the ternary gadget does **not** compute `1 + a + b + c` as a formal
polynomial. -/
theorem ternFactorSum_mvPolynomial {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (∑ h : Bool, ternGadgetBody τ (X 0 : MvPolynomial (Fin 3) F) (X 1) (X 2) (boolVal h))
      = (1 + X 0 + X 1 + X 2)
        + algebraMap F (MvPolynomial (Fin 3) F) (kappaVal τ)⁻¹ * (X 0 * X 1 * X 2) :=
  ternFactor_identity hτ0 hτ1 _ _ _

omit [CharP F 2] in
/-- **Firewall.**  `a b c (1 + a b) = 0` is *not* a formal polynomial identity: the
polynomial `X 0 * X 1 * X 2 * (1 + X 0 * X 1)` is nonzero in `MvPolynomial (Fin 3) F`.
Hence the cubic error may only be killed pointwise on Boolean assignments. -/
theorem cubic_error_not_formally_zero :
    (X 0 * X 1 * X 2 * (1 + X 0 * X 1) : MvPolynomial (Fin 3) F) ≠ 0 := by
  intro h
  have h2 := congrArg
    (aeval (fun i : Fin 3 => if i = 0 then (Polynomial.X : Polynomial F) else 1)) h
  simp only [map_mul, map_add, map_one, map_zero, aeval_X] at h2
  norm_num at h2
  have hc := congrArg (fun p : Polynomial F => p.coeff 1) h2
  simp [Polynomial.coeff_one] at hc

end MvPoly

end VNP1Char2
