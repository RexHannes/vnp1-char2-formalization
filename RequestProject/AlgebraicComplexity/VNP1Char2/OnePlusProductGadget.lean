/-
# The `1 + x y` gadget as four affine factors

`gadgetFactors τ x y b e` is the explicit list of the four affine forms

```
Δ⁻¹ (x + b + τ e),   x + τ b + τ² e + c,   τ⁴ y + b + (τ+1) e,   τ⁴ y + τ b + (τ²+τ) e + c
```

(the factor `Δ⁻¹` of the identity is folded into the first factor, which keeps it affine).
Their product, at Boolean values of the two fresh auxiliaries `b` and `e`, is the body
`J_τ` of the four-factor identity, so summing over the four Boolean values gives `1 + x y`.

Crucially each factor mentions the variables of `x` (or of `y`) plus the two fresh
auxiliaries, so if `x` and `y` are single variables the four factors have support `3`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.AffineForm
import RequestProject.AlgebraicComplexity.VNP1Char2.FourFactorIdentity

set_option maxRecDepth 8000

namespace VNP1Char2

open scoped BigOperators
open AffineForm

variable {σ : Type*} {F : Type*} [Field F] [CharP F 2] {M : Type*} [CommRing M] [Algebra F M]

/-- The four affine factors of the gadget expanding `1 + x*y`, using the two fresh Boolean
auxiliaries indexed by `bIdx` and `eIdx`. -/
def gadgetFactors (τ : F) (x y : AffineForm σ F) (bIdx eIdx : σ) : List (AffineForm σ F) :=
  [ scaleShift (deltaVal τ)⁻¹ x 0 [((deltaVal τ)⁻¹, bIdx), ((deltaVal τ)⁻¹ * τ, eIdx)],
    scaleShift 1 x (cVal τ) [(τ, bIdx), (τ ^ 2, eIdx)],
    scaleShift (τ ^ 4) y 0 [(1, bIdx), (τ + 1, eIdx)],
    scaleShift (τ ^ 4) y (cVal τ) [(τ, bIdx), (τ ^ 2 + τ, eIdx)] ]

@[simp] theorem length_gadgetFactors (τ : F) (x y : AffineForm σ F) (bIdx eIdx : σ) :
    (gadgetFactors τ x y bIdx eIdx).length = 4 := rfl

/-- Every gadget factor mentions at most two variables more than `x` resp. `y`. -/
theorem numVars_gadgetFactors_le {τ : F} {x y : AffineForm σ F} {bIdx eIdx : σ}
    {A : AffineForm σ F} (hA : A ∈ gadgetFactors τ x y bIdx eIdx) :
    A.numVars ≤ max x.numVars y.numVars + 2 := by
  fin_cases hA <;> simp <;> omega

/-- The product of the four gadget factors is the body of the four-factor identity. -/
theorem prod_gadgetFactors (τ : F) (x y : AffineForm σ F) (bIdx eIdx : σ) (g : σ → M)
    (b e : Bool) (hb : g bIdx = boolVal b) (he : g eIdx = boolVal e) :
    ((gadgetFactors τ x y bIdx eIdx).map fun A => A.eval g).prod
      = gadgetBody τ (x.eval g) (y.eval g) (boolVal b) (boolVal e) := by
  set T := algebraMap F M τ with hT
  set D := algebraMap F M (deltaVal τ)⁻¹ with hD
  set X := x.eval g with hX
  set Y := y.eval g with hY
  have h1 : (scaleShift (deltaVal τ)⁻¹ x 0
      [((deltaVal τ)⁻¹, bIdx), ((deltaVal τ)⁻¹ * τ, eIdx)]).eval g
        = D * (X + LVal T (boolVal b) (boolVal e)) := by
    rw [eval_scaleShift]
    simp only [hb, he, LVal, map_zero, map_mul, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ← hT, ← hD, ← hX]
    ring
  have h2 : (scaleShift 1 x (cVal τ) [(τ, bIdx), (τ ^ 2, eIdx)]).eval g
      = X + T * LVal T (boolVal b) (boolVal e) + cVal T := by
    rw [eval_scaleShift]
    simp only [hb, he, LVal, cVal, map_add, map_mul, map_pow, map_one, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, ← hT, ← hX]
    ring
  have h3 : (scaleShift (τ ^ 4) y 0 [(1, bIdx), (τ + 1, eIdx)]).eval g
      = T ^ 4 * Y + MVal T (boolVal b) (boolVal e) := by
    rw [eval_scaleShift]
    simp only [hb, he, MVal, map_zero, map_add, map_mul, map_pow, map_one, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, ← hT, ← hY]
    ring
  have h4 : (scaleShift (τ ^ 4) y (cVal τ) [(τ, bIdx), (τ ^ 2 + τ, eIdx)]).eval g
      = T ^ 4 * Y + T * MVal T (boolVal b) (boolVal e) + cVal T := by
    rw [eval_scaleShift]
    simp only [hb, he, MVal, cVal, map_add, map_mul, map_pow, map_one, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, ← hT, ← hY]
    ring
  have hassoc : ∀ p1 p2 p3 p4 : M, D * p1 * p2 * (p3 * p4) = D * (p1 * p2 * (p3 * p4)) := by
    intro p1 p2 p3 p4; ring
  simp only [gadgetFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    h1, h2, h3, h4]
  rw [← mul_assoc, hassoc]
  rfl

/-- Summing the product of the four gadget factors over the two Boolean auxiliaries gives
`1 + x y`. -/
theorem sum_prod_gadgetFactors {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (x y : AffineForm σ F)
    (bIdx eIdx : σ) (g : Bool → Bool → σ → M)
    (hb : ∀ b e, g b e bIdx = boolVal b) (he : ∀ b e, g b e eIdx = boolVal e)
    (hx : ∀ b e, x.eval (g b e) = x.eval (g false false))
    (hy : ∀ b e, y.eval (g b e) = y.eval (g false false)) :
    (∑ b : Bool, ∑ e : Bool,
        ((gadgetFactors τ x y bIdx eIdx).map fun A => A.eval (g b e)).prod)
      = 1 + x.eval (g false false) * y.eval (g false false) := by
  have hstep : ∀ b e : Bool,
      ((gadgetFactors τ x y bIdx eIdx).map fun A => A.eval (g b e)).prod
        = gadgetBody τ (x.eval (g false false)) (y.eval (g false false)) (boolVal b)
            (boolVal e) := by
    intro b e
    rw [prod_gadgetFactors τ x y bIdx eIdx (g b e) b e (hb b e) (he b e), hx b e, hy b e]
  simp_rw [hstep]
  exact fourFactor_identity hτ0 hτ1 _ _

end VNP1Char2
