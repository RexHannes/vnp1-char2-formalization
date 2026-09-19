/-
# Boolean embedding for the characteristic-two VNP₁ formalization layer

This file provides the tiny amount of "Boolean hypercube" infrastructure that the rest of
the layer consumes.  A Boolean auxiliary is a term of `Bool`; it is embedded into a
commutative ring by `boolVal`.

We deliberately avoid a general Boolean-algebra framework: only the identities actually
used later are proved here.
-/
import Mathlib

namespace VNP1Char2

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Embedding of a Boolean auxiliary into a commutative ring. -/
def boolVal : Bool → R
  | false => 0
  | true => 1

@[simp] theorem boolVal_false : (boolVal false : R) = 0 := rfl

@[simp] theorem boolVal_true : (boolVal true : R) = 1 := rfl

theorem boolVal_eq_zero_or_one (b : Bool) : (boolVal b : R) = 0 ∨ (boolVal b : R) = 1 := by
  cases b <;> simp

@[simp] theorem boolVal_mul_self (b : Bool) : (boolVal b : R) * boolVal b = boolVal b := by
  cases b <;> simp

/-- A Boolean sum of `1` vanishes in characteristic two.  This is the reason why the
compiler must never introduce a summed Boolean variable that does not occur in the body:
see `HypercubeFlattening`. -/
theorem sum_bool_one (h2 : (2 : R) = 0) : (∑ _b : Bool, (1 : R)) = 0 := by
  simp [Fintype.sum_bool]
  linear_combination h2

/-- Summing a function of a Boolean over the two Boolean values. -/
theorem sum_bool (f : Bool → R) : (∑ b : Bool, f b) = f false + f true := by
  simp [Fintype.sum_bool, add_comm]

/-- The "delta at zero" factor `∏ a, (1 + u a)` equals `1` at the all-false point. -/
theorem prod_one_add_boolVal_eq_one {α : Type*} [Fintype α] (u : α → Bool)
    (h : ∀ a, u a = false) : (∏ a : α, (1 + boolVal (u a) : R)) = 1 :=
  Finset.prod_eq_one fun a _ => by simp [h a]

end VNP1Char2
