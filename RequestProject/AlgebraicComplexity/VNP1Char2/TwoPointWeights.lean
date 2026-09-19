/-
# The two-point weight identity behind the local arithmetic threshold

This small module records, for any field, the elementary two-point interpolation identity
that explains *why* the local gadgets need two distinct nonzero field elements — that is,
why `|F| > 2` is exactly the arithmetic threshold.

For distinct nonzero `r, s` put

```
w_r = s / (s - r),     w_s = -r / (s - r),     μ = -r s.
```

Then `w_r + w_s = 1`, `w_r r + w_s s = 0`, `w_r r² + w_s s² = μ`, and therefore

```
w_r (x + r)(μ y + r) + w_s (x + s)(μ y + s) = μ (1 + x y)
```

for *arbitrary* `x, y`.  Taking `r = τ`, `s = τ + 1` in characteristic two gives
`s - r = 1` and `μ = τ(τ+1) = κ`, which is the two-term form of the banked one-bit
`1 + x y` gadget.  Nothing else in the direct compiler depends on this module.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.DirectBranchGadget

namespace VNP1Char2

variable {F : Type*} [Field F]

/-- The first interpolation weight. -/
noncomputable def weightR (r s : F) : F := s / (s - r)

/-- The second interpolation weight. -/
noncomputable def weightS (r s : F) : F := -r / (s - r)

/-- The scaling constant `μ = -r s`. -/
def muVal (r s : F) : F := -(r * s)

theorem weight_sum {r s : F} (hrs : r ≠ s) : weightR r s + weightS r s = 1 := by
  have h : s - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
  unfold weightR weightS
  field_simp
  ring

theorem weight_first_moment {r s : F} (hrs : r ≠ s) :
    weightR r s * r + weightS r s * s = 0 := by
  have h : s - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
  unfold weightR weightS
  field_simp
  ring

theorem weight_second_moment {r s : F} (hrs : r ≠ s) :
    weightR r s * r ^ 2 + weightS r s * s ^ 2 = muVal r s := by
  have h : s - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
  unfold weightR weightS muVal
  field_simp
  ring

/-- **The two-point `1 + x y` identity.**  For distinct `r, s` the two weighted products of
affine forms reproduce `μ (1 + x y)` for arbitrary `x, y`. -/
theorem two_point_identity {r s : F} (hrs : r ≠ s) (x y : F) :
    weightR r s * ((x + r) * (muVal r s * y + r))
        + weightS r s * ((x + s) * (muVal r s * y + s))
      = muVal r s * (1 + x * y) := by
  have h : s - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
  unfold weightR weightS muVal
  field_simp
  ring

/-- In characteristic two, the choice `r = τ`, `s = τ + 1` has `μ = κ = τ(τ+1)`, so the
two-point identity is the two-term form of the banked one-bit gadget.  Two distinct nonzero
elements exist exactly when `F` has more than two elements. -/
theorem muVal_tau_succ [CharP F 2] (τ : F) : muVal τ (τ + 1) = kappaVal τ := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  simp only [muVal, kappaVal]
  linear_combination (-(τ * (τ + 1))) * h2

end VNP1Char2
