/-
# The direct one-bit six-factor branch gadget

This is a new, strictly append-only module.  Nothing in the frozen graph/path layer is
modified, reproved or used here.

Over a field `F` of characteristic two with `τ ≠ 0`, `τ ≠ 1`, and with

```
κ = τ (τ + 1)   (`kappaVal`),
```

the *branch gadget* is the product of the six affine factors

```
1 + (1 + κ⁻¹) h,
c + τ h,
c + (τ+1) h,
1 + ((τ+1)/τ) b + (1/τ) h,
1 + (τ/(τ+1)) a + (1/(τ+1)) h,
1 + τ a + (τ+1) b,
```

each of which mentions **at most two** variables — respectively `h`, `(c,h)`, `(c,h)`,
`(b,h)`, `(a,h)`, `(a,b)`.  The gadget consumes a single fresh Boolean auxiliary `h`.

**(BRANCH)** For *Boolean* `a, b, c`,

```
∑_{h ∈ {0,1}} Γ_τ(a,b,c;h) = (1 + a + b + c)(1 + a b),
```

whose Boolean support is exactly `{(0,0,0), (1,0,1), (0,1,1)}`: reading `c` as the
activation of a node and `a, b` as the activations of its two children, an inactive parent
forces both children inactive, and an active parent activates exactly one child.

**Scope firewall.**  `(BRANCH)` is asserted *only* for Boolean `a, b, c`; it is not claimed
as an unrestricted polynomial identity, and the file `RegressionTestsDirect.lean` records
an explicit refutation of the unrestricted statement.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.SupportTwoGadget

namespace VNP1Char2

open scoped BigOperators
open AffineForm

variable {σ : Type*} {F : Type*} [Field F] {M : Type*} [CommRing M] [Algebra F M]

/-! ## The branch body and the Boolean identity -/

/-- The six-factor branch body `Γ_τ(A,B,C;H)`, as an element of the base field. -/
noncomputable def branchBody (τ A B C H : F) : F :=
  (1 + (1 + (kappaVal τ)⁻¹) * H) * (C + τ * H) * (C + (τ + 1) * H)
    * (1 + (τ + 1) / τ * B + 1 / τ * H) * (1 + τ / (τ + 1) * A + 1 / (τ + 1) * H)
    * (1 + τ * A + (τ + 1) * B)

/-- **(BRANCH).**  Summing the branch body over the single Boolean auxiliary `h` gives
`(1 + a + b + c)(1 + a b)` for *Boolean* `a, b, c`. -/
theorem branch_identity [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (a b c : Bool) :
    (∑ h : Bool, branchBody τ (boolVal a) (boolVal b) (boolVal c) (boolVal h))
      = (1 + boolVal a + boolVal b + boolVal c) * (1 + boolVal a * boolVal b) := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hv : τ + 1 ≠ 0 := fun h => hτ1 (by rw [add_eq_zero_iff_eq_neg.mp h, CharTwo.neg_eq])
  cases a <;> cases b <;> cases c <;>
    simp only [boolVal, branchBody, kappaVal, Fintype.sum_bool] <;>
    field_simp <;> ring_nf
  · linear_combination (τ + 4*τ^2 + 8*τ^3 + 9*τ^4 + 5*τ^5 + τ^6) * h2
  · linear_combination (2 + 10*τ + 22*τ^2 + 27*τ^3 + 19*τ^4 + 7*τ^5 + τ^6) * h2
  · linear_combination (4*τ + 19*τ^2 + 43*τ^3 + 55*τ^4 + 39*τ^5 + 14*τ^6 + 2*τ^7) * h2
  · linear_combination (8 + 45*τ + 113*τ^2 + 161*τ^3 + 137*τ^4 + 68*τ^5 + 18*τ^6 + 2*τ^7) * h2
  · linear_combination (τ + 5*τ^2 + 14*τ^3 + 23*τ^4 + 21*τ^5 + 10*τ^6 + 2*τ^7) * h2
  · linear_combination (2 + 13*τ + 37*τ^2 + 63*τ^3 + 67*τ^4 + 42*τ^5 + 14*τ^6 + 2*τ^7) * h2
  · linear_combination (4*τ + 21*τ^2 + 58*τ^3 + 93*τ^4 + 84*τ^5 + 40*τ^6 + 8*τ^7) * h2
  · linear_combination (8 + 53*τ + 154*τ^2 + 261*τ^3 + 272*τ^4 + 168*τ^5 + 56*τ^6 + 8*τ^7) * h2

/-- The Boolean predicate describing the three states allowed by the branch gadget:
parent inactive with both children inactive, or parent active with exactly one active
child. -/
def BranchAllowed (a b c : Bool) : Prop :=
  (a, b, c) = (false, false, false) ∨ (a, b, c) = (true, false, true) ∨
    (a, b, c) = (false, true, true)

instance (a b c : Bool) : Decidable (BranchAllowed a b c) := by
  unfold BranchAllowed; infer_instance

/-- **The branch truth table.**  For all eight Boolean states, the Boolean sum of the
branch body is `1` on the three allowed states and `0` on the other five. -/
theorem branch_truth_table [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (a b c : Bool) :
    (∑ h : Bool, branchBody τ (boolVal a) (boolVal b) (boolVal c) (boolVal h))
      = if BranchAllowed a b c then 1 else 0 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  rw [branch_identity hτ0 hτ1]
  cases a <;> cases b <;> cases c <;>
    simp only [boolVal, BranchAllowed, Prod.mk.injEq] <;>
    norm_num <;>
    first
      | linear_combination h2
      | linear_combination (2 : F) * h2
      | linear_combination (3 : F) * h2
      | linear_combination (4 : F) * h2

/-! ## The branch gadget as a list of affine forms -/

/-- The six affine factors of the branch gadget, with parent index `cIdx`, child indices
`aIdx`, `bIdx` and the single fresh Boolean auxiliary `hIdx`. -/
noncomputable def branchFactors (τ : F) (aIdx bIdx cIdx hIdx : σ) : List (AffineForm σ F) :=
  [ ⟨1, [(1 + (kappaVal τ)⁻¹, hIdx)]⟩,
    ⟨0, [(1, cIdx), (τ, hIdx)]⟩,
    ⟨0, [(1, cIdx), (τ + 1, hIdx)]⟩,
    ⟨1, [((τ + 1) / τ, bIdx), (1 / τ, hIdx)]⟩,
    ⟨1, [(τ / (τ + 1), aIdx), (1 / (τ + 1), hIdx)]⟩,
    ⟨1, [(τ, aIdx), (τ + 1, bIdx)]⟩ ]

@[simp] theorem length_branchFactors (τ : F) (aIdx bIdx cIdx hIdx : σ) :
    (branchFactors τ aIdx bIdx cIdx hIdx).length = 6 := rfl

/-- **Support two.**  Every affine factor of the branch gadget mentions at most two
variables. -/
theorem numVars_branchFactors_le {τ : F} {aIdx bIdx cIdx hIdx : σ} {A : AffineForm σ F}
    (hA : A ∈ branchFactors τ aIdx bIdx cIdx hIdx) : A.numVars ≤ 2 := by
  fin_cases hA <;> simp [numVars]

/-- The product of the six affine factors, evaluated at an assignment sending the four
gadget indices to (the images of) field elements, is the branch body. -/
theorem prod_branchFactors (τ : F) (aIdx bIdx cIdx hIdx : σ) (g : σ → M) (A B C H : F)
    (ga : g aIdx = algebraMap F M A) (gb : g bIdx = algebraMap F M B)
    (gc : g cIdx = algebraMap F M C) (gh : g hIdx = algebraMap F M H) :
    ((branchFactors τ aIdx bIdx cIdx hIdx).map fun P => P.eval g).prod
      = algebraMap F M (branchBody τ A B C H) := by
  simp only [branchFactors, branchBody, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, AffineForm.eval, List.sum_cons, List.sum_nil, ga, gb, gc, gh,
    map_mul, map_add, map_one, map_zero]
  ring

/-- **The branch gadget in an algebra.**  Summing the product of the six affine factors
over the single fresh Boolean auxiliary gives `1` on the three allowed activation states
and `0` on the other five. -/
theorem sum_prod_branchFactors [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    (aIdx bIdx cIdx hIdx : σ) (g : Bool → σ → M) (a b c : Bool)
    (ga : ∀ h, g h aIdx = algebraMap F M (boolVal a))
    (gb : ∀ h, g h bIdx = algebraMap F M (boolVal b))
    (gc : ∀ h, g h cIdx = algebraMap F M (boolVal c))
    (gh : ∀ h, g h hIdx = algebraMap F M (boolVal h)) :
    (∑ h : Bool, ((branchFactors τ aIdx bIdx cIdx hIdx).map fun P => P.eval (g h)).prod)
      = if BranchAllowed a b c then 1 else 0 := by
  have hstep : ∀ h : Bool,
      ((branchFactors τ aIdx bIdx cIdx hIdx).map fun P => P.eval (g h)).prod
        = algebraMap F M (branchBody τ (boolVal a) (boolVal b) (boolVal c) (boolVal h)) :=
    fun h => prod_branchFactors τ aIdx bIdx cIdx hIdx (g h) _ _ _ _ (ga h) (gb h) (gc h) (gh h)
  simp_rw [hstep]
  rw [← map_sum, branch_truth_table hτ0 hτ1]
  by_cases hA : BranchAllowed a b c <;> simp [hA]

end VNP1Char2
