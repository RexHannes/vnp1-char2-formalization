/-
# The support-two gadgets as lists of affine forms

Two gadgets, each consuming **one** fresh Boolean auxiliary `hIdx`:

* `gadget2Factors τ x y hIdx` — three affine forms

```
κ⁻¹(τ+1) + κ⁻¹ h,      x + τ + h,      κ y + τ + h
```

whose product is `twoGadgetBody τ x y h`, so that summing over `h ∈ {0,1}` gives `1 + x y`.
If `x` and `y` are single variables (or constants) all three factors have support `≤ 2`.

* `ternFactors τ a b c hIdx` — four affine forms

```
κ⁻¹(τ+1) + κ⁻¹ h,      a + τ + h,      b + τ + h,      c + τ + h
```

in three *variables* `a, b, c`, whose product is `ternGadgetBody τ a b c h`; summing over
`h ∈ {0,1}` gives `1 + a + b + c` **plus the cubic error** `κ⁻¹ a b c`.  Each factor has
support `≤ 2`.

Freshness is not assumed here: it is enforced by the index types used in `CompilerTwo.lean`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.AffineForm
import RequestProject.AlgebraicComplexity.VNP1Char2.TernaryIdentity

namespace VNP1Char2

open scoped BigOperators
open AffineForm

variable {σ : Type*} {F : Type*} [Field F] {M : Type*} [CommRing M] [Algebra F M]

/-! ## The quadratic `1 + x y` gadget -/

/-- The three affine factors of the support-two gadget expanding `1 + x*y`, using the
single fresh Boolean auxiliary indexed by `hIdx`. -/
def gadget2Factors (τ : F) (x y : AffineForm σ F) (hIdx : σ) : List (AffineForm σ F) :=
  [ ⟨(kappaVal τ)⁻¹ * (τ + 1), [((kappaVal τ)⁻¹, hIdx)]⟩,
    scaleShift 1 x τ [(1, hIdx)],
    scaleShift (kappaVal τ) y τ [(1, hIdx)] ]

@[simp] theorem length_gadget2Factors (τ : F) (x y : AffineForm σ F) (hIdx : σ) :
    (gadget2Factors τ x y hIdx).length = 3 := rfl

/-- Every factor of the quadratic gadget mentions at most one variable more than `x`
resp. `y`. -/
theorem numVars_gadget2Factors_le {τ : F} {x y : AffineForm σ F} {hIdx : σ}
    {A : AffineForm σ F} (hA : A ∈ gadget2Factors τ x y hIdx) :
    A.numVars ≤ max x.numVars y.numVars + 1 := by
  fin_cases hA <;>
    simp only [numVars, scaleShift, List.length_append, List.length_map, List.length_cons,
      List.length_nil] <;> omega

/-- The product of the three gadget factors is the support-two gadget body. -/
theorem prod_gadget2Factors (τ : F) (x y : AffineForm σ F) (hIdx : σ) (g : σ → M) (h : Bool)
    (hh : g hIdx = boolVal h) :
    ((gadget2Factors τ x y hIdx).map fun A => A.eval g).prod
      = twoGadgetBody τ (x.eval g) (y.eval g) (boolVal h) := by
  have h1 : (⟨(kappaVal τ)⁻¹ * (τ + 1), [((kappaVal τ)⁻¹, hIdx)]⟩ : AffineForm σ F).eval g
      = algebraMap F M (kappaVal τ)⁻¹ *
        (algebraMap F M τ + 1 + boolVal h) := by
    simp only [AffineForm.eval, hh, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      map_mul, map_add, map_one]
    ring
  have h2 : (scaleShift 1 x τ [(1, hIdx)]).eval g = x.eval g + algebraMap F M τ + boolVal h := by
    rw [eval_scaleShift]
    simp only [hh, map_one, one_mul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  have h3 : (scaleShift (kappaVal τ) y τ [(1, hIdx)]).eval g
      = kappaVal (algebraMap F M τ) * y.eval g + algebraMap F M τ + boolVal h := by
    rw [eval_scaleShift, kappaVal_algebraMap]
    simp only [hh, map_one, one_mul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  simp only [gadget2Factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h1, h2, h3, twoGadgetBody, twoFactorBody]
  ring

/-- **The quadratic gadget expands `1 + x y`.**  Summing the product of the three affine
factors over the single fresh Boolean auxiliary gives `1 + x y`. -/
theorem sum_prod_gadget2Factors [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (x y : AffineForm σ F)
    (hIdx : σ) (g : Bool → σ → M) (hh : ∀ h, g h hIdx = boolVal h)
    (hx : ∀ h, x.eval (g h) = x.eval (g false)) (hy : ∀ h, y.eval (g h) = y.eval (g false)) :
    (∑ h : Bool, ((gadget2Factors τ x y hIdx).map fun A => A.eval (g h)).prod)
      = 1 + x.eval (g false) * y.eval (g false) := by
  have hstep : ∀ h : Bool, ((gadget2Factors τ x y hIdx).map fun A => A.eval (g h)).prod
      = twoGadgetBody τ (x.eval (g false)) (y.eval (g false)) (boolVal h) := by
    intro h
    rw [prod_gadget2Factors τ x y hIdx (g h) h (hh h), hx h, hy h]
  simp_rw [hstep]
  exact twoFactor_identity hτ0 hτ1 _ _

/-! ## The ternary flow gadget -/

/-- The four affine factors of the ternary gadget expanding `1 + a + b + c` (up to the
cubic error), using the single fresh Boolean auxiliary indexed by `hIdx`.  The inputs
`a, b, c` are *variables*, so every factor has support at most two. -/
def ternFactors (τ : F) (a b c hIdx : σ) : List (AffineForm σ F) :=
  [ ⟨(kappaVal τ)⁻¹ * (τ + 1), [((kappaVal τ)⁻¹, hIdx)]⟩,
    ⟨τ, [(1, a), (1, hIdx)]⟩,
    ⟨τ, [(1, b), (1, hIdx)]⟩,
    ⟨τ, [(1, c), (1, hIdx)]⟩ ]

@[simp] theorem length_ternFactors (τ : F) (a b c hIdx : σ) :
    (ternFactors (F := F) τ a b c hIdx).length = 4 := rfl

/-- **Support two.**  Every factor of the ternary gadget mentions at most two variables. -/
theorem numVars_ternFactors_le {τ : F} {a b c hIdx : σ} {A : AffineForm σ F}
    (hA : A ∈ ternFactors (F := F) τ a b c hIdx) : A.numVars ≤ 2 := by
  fin_cases hA <;> simp [numVars]

theorem eval_ternFactors_aux (τ : F) (i hIdx : σ) (g : σ → M) :
    (⟨τ, [(1, i), (1, hIdx)]⟩ : AffineForm σ F).eval g = g i + algebraMap F M τ + g hIdx := by
  simp only [AffineForm.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, map_one,
    one_mul]
  ring

/-- The product of the four ternary factors is the ternary gadget body. -/
theorem prod_ternFactors (τ : F) (a b c hIdx : σ) (g : σ → M) (h : Bool)
    (hh : g hIdx = boolVal h) :
    ((ternFactors (F := F) τ a b c hIdx).map fun A => A.eval g).prod
      = ternGadgetBody τ (g a) (g b) (g c) (boolVal h) := by
  have h1 : (⟨(kappaVal τ)⁻¹ * (τ + 1), [((kappaVal τ)⁻¹, hIdx)]⟩ : AffineForm σ F).eval g
      = algebraMap F M (kappaVal τ)⁻¹ * (algebraMap F M τ + 1 + boolVal h) := by
    simp only [AffineForm.eval, hh, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      map_mul, map_add, map_one]
    ring
  simp only [ternFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h1, eval_ternFactors_aux, hh, ternGadgetBody, ternFactorBody]
  ring

/-- **The ternary gadget expands `1 + a + b + c` up to the cubic error.**  Summing the
product of the four affine factors over the single fresh Boolean auxiliary gives
`(1 + a + b + c) + κ⁻¹ a b c`.  The error term is real: it is *not* zero as a formal
polynomial. -/
theorem sum_prod_ternFactors [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (a b c hIdx : σ)
    (g : Bool → σ → M) (hh : ∀ h, g h hIdx = boolVal h)
    (ha : ∀ h, g h a = g false a) (hb : ∀ h, g h b = g false b) (hc : ∀ h, g h c = g false c) :
    (∑ h : Bool, ((ternFactors (F := F) τ a b c hIdx).map fun A => A.eval (g h)).prod)
      = (1 + g false a + g false b + g false c)
        + algebraMap F M (kappaVal τ)⁻¹ * (g false a * g false b * g false c) := by
  have hstep : ∀ h : Bool, ((ternFactors (F := F) τ a b c hIdx).map fun A => A.eval (g h)).prod
      = ternGadgetBody τ (g false a) (g false b) (g false c) (boolVal h) := by
    intro h
    rw [prod_ternFactors τ a b c hIdx (g h) h (hh h), ha h, hb h, hc h]
  simp_rw [hstep]
  exact ternFactor_identity hτ0 hτ1 _ _ _

end VNP1Char2
