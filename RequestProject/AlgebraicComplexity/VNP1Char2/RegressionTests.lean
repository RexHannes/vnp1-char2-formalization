/-
# Regression / firewall tests

These theorems are *negative* results.  They are not used anywhere in the compiler; their
purpose is to pin down the exact scope of the positive theorems, so that a later
generalisation attempt fails to compile instead of silently overstating a claim.

* `tau_zero_fails`, `tau_one_fails` : the excluded values `τ = 0` and `τ = 1` genuinely
  break the four-factor identity (this is also why the construction cannot work over `F₂`,
  where those are the only field elements).
* `shared_auxiliary_changes_result` : the false step
  `(∑_b A b)(∑_b B b) = ∑_b A b B b` really is false, so gadget auxiliaries must be fresh.
* `sum_bool_const_eq_zero` : a completely unused summed Boolean variable annihilates the
  representation in characteristic two, so no such variable may be introduced.
* `unrestricted_label_support_firewall` : for an edge labelled `x₁ + x₂ + x₃` the
  edge-selector gadget produces an affine factor of support `5 > 3`, so the support bound
  is *not* a theorem about arbitrary ABPs with arbitrary affine labels — it is a theorem
  about formula-generated graphs, whose labels are single variables or constants.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.SupportThree

namespace VNP1Char2

open scoped BigOperators
open AffineForm

section Algebraic

variable {F : Type*} [Field F] [CharP F 2]

/-- `τ = 0` is genuinely excluded: the gadget body degenerates to `0`, and the four-factor
sum is `0 ≠ 1 + x·y` already for `x = y = 0`. -/
theorem tau_zero_fails :
    (∑ b : Bool, ∑ e : Bool, gadgetBody (0 : F) (0 : F) 0 (boolVal b) (boolVal e))
      ≠ 1 + (0 : F) * 0 := by
  have hbody : ∀ b e : F, gadgetBody (0 : F) (0 : F) 0 b e = 0 := by
    intro b e
    simp [gadgetBody, deltaVal]
  simp [hbody]

/-- `τ = 1` is genuinely excluded, for the same reason: `Δ = τ⁴(τ+1)² = 0` in characteristic
two. -/
theorem tau_one_fails :
    (∑ b : Bool, ∑ e : Bool, gadgetBody (1 : F) (0 : F) 0 (boolVal b) (boolVal e))
      ≠ 1 + (0 : F) * 0 := by
  have hbody : ∀ b e : F, gadgetBody (1 : F) (0 : F) 0 b e = 0 := by
    intro b e
    simp [gadgetBody, delta_eq_zero_of_eq_one (F := F)]
  simp [hbody]

/-- **Freshness firewall.**  Identifying the summation variables of two different gadgets
changes the value: `(∑_b A b)(∑_b B b) ≠ ∑_b A b · B b` in general. -/
theorem shared_auxiliary_changes_result :
    ((∑ b : Bool, (boolVal b : F)) * ∑ b : Bool, (1 + boolVal b : F))
      ≠ ∑ b : Bool, (boolVal b : F) * (1 + boolVal b) := by
  have h2 : (1 : F) + 1 = 0 := by
    have : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    linear_combination this
  rw [sum_bool, sum_bool, sum_bool]
  simp only [boolVal]
  rw [show (0 : F) + 1 = 1 by ring, show (1 : F) + 0 = 1 by ring]
  rw [h2]
  simpa using one_ne_zero (α := F)

/-- **Unused-auxiliary firewall.**  In characteristic two a summed Boolean variable that
occurs in no factor annihilates the whole representation. -/
theorem sum_bool_const_eq_zero (x : F) : (∑ _b : Bool, x) = 0 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  rw [sum_bool]
  linear_combination x * h2

end Algebraic

section Support

variable {F : Type*} [Field F] [CharP F 2]

/-- The affine label `x₁ + x₂ + x₃` on a single edge. -/
def threeVarLabel : AffineForm (Fin 6) F := ⟨0, [(1, 0), (1, 1), (1, 2)]⟩

/-- **Support-scope firewall.**  Feeding an edge label of support three into the
edge-selector gadget produces an affine factor of support `5`.  Hence `SUPPORT3` is false
for unrestricted algebraic branching programs, and the positive theorem is correctly stated
only for the formula-generated graphs, whose labels have support at most one. -/
theorem unrestricted_label_support_firewall (τ : F) :
    ∃ A ∈ gadgetFactors τ (threeVarLabel : AffineForm (Fin 6) F) (varForm 5) 3 4,
      3 < A.vars.card := by
  refine ⟨scaleShift (deltaVal τ)⁻¹ (threeVarLabel : AffineForm (Fin 6) F) 0
      [((deltaVal τ)⁻¹, 3), ((deltaVal τ)⁻¹ * τ, 4)], by simp [gadgetFactors], ?_⟩
  have hv : (scaleShift (deltaVal τ)⁻¹ (threeVarLabel : AffineForm (Fin 6) F) 0
      [((deltaVal τ)⁻¹, 3), ((deltaVal τ)⁻¹ * τ, 4)]).vars = {0, 1, 2, 3, 4} := by
    simp [scaleShift, threeVarLabel, vars]
  rw [hv]
  decide

end Support

end VNP1Char2
