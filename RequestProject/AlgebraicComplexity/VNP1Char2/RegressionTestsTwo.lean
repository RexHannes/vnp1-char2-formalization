/-
# Regression / firewall tests for the support-two layer

These theorems are *negative* results.  They are not used anywhere in the compiler; their
purpose is to pin down the exact scope of the support-two theorems, so that a later
generalisation attempt fails to compile instead of silently overstating a claim.

* `kappa_tau_zero_fails`, `kappa_tau_one_fails` : the excluded values `τ = 0` and `τ = 1`
  genuinely break the support-two gadget (`κ = τ(τ+1) = 0`); this is also why the
  construction cannot work over `F₂`, where those are the only field elements.
* `cubic_error_not_formally_zero` (in `TernaryIdentity.lean`) : `a b c (1 + a b)` is **not**
  the zero polynomial, so the cubic error of the ternary gadget may only be killed
  pointwise, on Boolean assignments.  `ternary_error_nonzero_without_exclusion` records the
  same fact at the level of the ternary body: its Boolean sum differs from `1 + a + b + c`.
* `shared_one_bit_auxiliary_changes_result` : the one-auxiliary version of the freshness
  firewall, `(∑_h A h)(∑_h B h) ≠ ∑_h A h · B h`.
* `unrestricted_label_supportTwo_firewall` : for an edge labelled `x₁ + x₂ + x₃` the
  support-two edge-selector gadget produces an affine factor of support `4 > 2`, so
  `SUPPORT2` is *not* a theorem about arbitrary ABPs with arbitrary affine labels.
* `degree_three_flow_factor_support_three` : a flow factor at a degree-three vertex has
  support three, which is exactly why the ternary gadget is needed at all; and
  `single_variable_label_supportTwo` shows that with a one-variable label the gadget does
  stay within support two.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.GraphCompilerTwo

namespace VNP1Char2

open scoped BigOperators
open AffineForm

section Algebraic

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- `τ = 0` is genuinely excluded: `κ = 0`, the gadget body degenerates to `0`, and the
support-two sum is `0 ≠ 1 + x·y` already for `x = y = 0`. -/
theorem kappa_tau_zero_fails :
    (∑ h : Bool, twoGadgetBody (0 : F) (0 : F) 0 (boolVal h)) ≠ 1 + (0 : F) * 0 := by
  have hbody : ∀ h : F, twoGadgetBody (0 : F) (0 : F) 0 h = 0 := by
    intro h
    simp [twoGadgetBody, kappaVal]
  simp [hbody]

/-- `τ = 1` is genuinely excluded, for the same reason: `κ = τ(τ+1) = 0` in characteristic
two. -/
theorem kappa_tau_one_fails :
    (∑ h : Bool, twoGadgetBody (1 : F) (0 : F) 0 (boolVal h)) ≠ 1 + (0 : F) * 0 := by
  have hbody : ∀ h : F, twoGadgetBody (1 : F) (0 : F) 0 h = 0 := by
    intro h
    simp [twoGadgetBody, kappa_eq_zero_of_eq_one (F := F)]
  simp [hbody]

/-- **The ternary gadget really does not compute `1 + a + b + c` formally.**  Its Boolean
sum differs from the affine flow factor by the nonzero polynomial `κ⁻¹ a b c`; equality
holds only after the cubic error has been killed pointwise against a pair exclusion. -/
theorem ternary_error_nonzero_without_exclusion {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (∑ h : Bool, ternGadgetBody τ (MvPolynomial.X 0 : MvPolynomial (Fin 3) F)
        (MvPolynomial.X 1) (MvPolynomial.X 2) (boolVal h))
      ≠ 1 + MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 := by
  rw [ternFactorSum_mvPolynomial hτ0 hτ1]
  intro hcon
  have herr : (algebraMap F (MvPolynomial (Fin 3) F) (kappaVal τ)⁻¹ *
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)) = 0 := by
    have := hcon
    linear_combination this
  have hκ : (kappaVal τ)⁻¹ ≠ 0 := inv_ne_zero (kappa_ne_zero hτ0 hτ1)
  rcases mul_eq_zero.mp herr with h | h
  · exact hκ ((map_eq_zero_iff _ (algebraMap F (MvPolynomial (Fin 3) F)).injective).mp h)
  · have hne : (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 :
        MvPolynomial (Fin 3) F) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> exact MvPolynomial.X_ne_zero _
    exact hne h

/-- **Freshness firewall, one-auxiliary version.**  Identifying the summation variable of
two different support-two gadgets changes the value. -/
theorem shared_one_bit_auxiliary_changes_result :
    ((∑ h : Bool, (boolVal h : F)) * ∑ h : Bool, (1 + boolVal h : F))
      ≠ ∑ h : Bool, (boolVal h : F) * (1 + boolVal h) := by
  have h2 : (1 : F) + 1 = 0 := by
    have : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    linear_combination this
  rw [sum_bool, sum_bool, sum_bool]
  simp only [boolVal]
  rw [show (0 : F) + 1 = 1 by ring, show (1 : F) + 0 = 1 by ring]
  rw [h2]
  simp

end Algebraic

section Support

variable {F : Type*} [Field F] [CharP F 2]

/-- The affine label `x₁ + x₂ + x₃` on a single edge. -/
def threeVarLabel2 : AffineForm (Fin 6) F := ⟨0, [(1, 0), (1, 1), (1, 2)]⟩

omit [CharP F 2] in
/-- **Support-scope firewall.**  Feeding an edge label of support three into the
support-two edge-selector gadget produces an affine factor of support `4`.  Hence
`SUPPORT2` is false for unrestricted algebraic branching programs, and the positive theorem
is correctly stated only for the formula-generated graphs, whose labels have support at
most one. -/
theorem unrestricted_label_supportTwo_firewall (τ : F) :
    ∃ A ∈ gadget2Factors τ (threeVarLabel2 : AffineForm (Fin 6) F) (varForm 5) 3,
      2 < A.vars.card := by
  refine ⟨scaleShift 1 (threeVarLabel2 : AffineForm (Fin 6) F) τ [(1, 3)],
    by simp [gadget2Factors], ?_⟩
  have hv : (scaleShift 1 (threeVarLabel2 : AffineForm (Fin 6) F) τ [(1, 3)]).vars
      = {0, 1, 2, 3} := by
    simp [scaleShift, threeVarLabel2, vars]
  rw [hv]
  decide

omit [CharP F 2] in
/-- With a one-variable label the support-two gadget does stay within support two. -/
theorem single_variable_label_supportTwo (τ : F) (A : AffineForm (Fin 6) F)
    (hA : A.numVars ≤ 1) (i : Fin 6) :
    ∀ B ∈ gadget2Factors τ A (varForm i) 3, B.numVars ≤ 2 := by
  intro B hB
  have := numVars_gadget2Factors_le hB
  simp only [numVars_varForm] at this
  omega

end Support

section Degrees

variable {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {F : Type*} [Field F] [CharP F 2]

/-- **Why the ternary gadget is needed.**  At an internal vertex of total degree three the
flow factor mentions three selection variables, so it is *not* of support two and must be
expanded. -/
theorem degree_three_flow_factor_support_three (G : PathGraph V E) (v : V) (hs : v ≠ G.s)
    (ht : v ≠ G.t) (h3 : (G.inEdges v).card + (G.outEdges v).card = 3) :
    (PathGraph.flowAff (ι := ι) (F := F) G v).numVars = 3 := by
  rw [PathGraph.numVars_flowAff, if_neg hs, if_neg ht, h3]

end Degrees

end VNP1Char2
