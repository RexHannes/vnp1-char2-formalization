/-
# The generic quadratic → affine compiler

Input data:

* a finite type `A` of Boolean *selection* variables;
* a finite type `K` of *gadget occurrences*, each carrying two affine forms `x k`, `y k`
  in the original variables and the selection variables;
* a list `flowForms` of affine forms in the original variables and selection variables.

Output: an `AffineHypercubeRep` with auxiliaries `A ⊕ K × Bool` — the selection bits
together with **two fresh auxiliaries per gadget occurrence** — whose value is

```
∑_{z : A → Bool} (∏ flowForms(z)) * ∏_k (1 + x_k(z) y_k(z)),
```

i.e. the quadratic factors `1 + x_k y_k` have been replaced by products of affine factors
at the cost of `2|K|` extra summed Boolean variables and `4|K|` extra factors.

The freshness of the auxiliaries is built into the index type `K × Bool`: distinct gadget
occurrences use distinct auxiliaries, and the flattening lemma `prod_sum_flatten` is what
justifies exchanging the product over `k` with the sum over the auxiliary cube.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.OnePlusProductGadget
import RequestProject.AlgebraicComplexity.VNP1Char2.HypercubeFlattening

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace VNP1Char2

open scoped BigOperators
open AffineForm MvPolynomial

variable {ι A K : Type} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [CharP F 2]

/-- Substitution of the original indeterminates and of the Boolean selection values. -/
noncomputable def substSel (z : A → Bool) : (ι ⊕ A) → MvPolynomial ι F :=
  Sum.elim X fun a => boolVal (z a)

/-- The inclusion of the selection-variable index type into the full auxiliary index
type. -/
def embSel : (ι ⊕ A) → (ι ⊕ (A ⊕ K × Bool)) := Sum.map id Sum.inl

/-- The compiled representation: the flow factors, followed by four affine factors for
each gadget occurrence. -/
noncomputable def compiled (τ : F) (flowForms : List (AffineForm (ι ⊕ A) F))
    (x y : K → AffineForm (ι ⊕ A) F) : AffineHypercubeRep ι F where
  aux := A ⊕ K × Bool
  auxFintype := inferInstance
  auxDecEq := inferInstance
  factors := flowForms.map (mapVar embSel) ++
    (Finset.univ : Finset K).toList.flatMap fun k =>
      gadgetFactors τ (mapVar embSel (x k)) (mapVar embSel (y k))
        (Sum.inr (Sum.inr (k, false))) (Sum.inr (Sum.inr (k, true)))

namespace compiled

variable (τ : F) (flowForms : List (AffineForm (ι ⊕ A) F)) (x y : K → AffineForm (ι ⊕ A) F)

@[simp] theorem aux_eq : (compiled τ flowForms x y).aux = (A ⊕ K × Bool) := rfl

theorem factors_eq : (compiled τ flowForms x y).factors = flowForms.map (mapVar embSel) ++
    (Finset.univ : Finset K).toList.flatMap (fun k =>
      gadgetFactors τ (mapVar embSel (x k)) (mapVar embSel (y k))
        (Sum.inr (Sum.inr (k, false))) (Sum.inr (Sum.inr (k, true)))) := rfl

/-- **Size accounting, auxiliaries**: `q = |A| + 2|K|`. -/
theorem numAux_eq :
    (compiled τ flowForms x y).numAux = Fintype.card A + 2 * Fintype.card K := by
  show Fintype.card (A ⊕ K × Bool) = _
  simp [Fintype.card_sum, Fintype.card_prod, two_mul, mul_comm]

/-- **Size accounting, factors**: `M = #flowForms + 4|K|`. -/
theorem numFactors_eq :
    (compiled τ flowForms x y).numFactors = flowForms.length + 4 * Fintype.card K := by
  show (List.length _) = _
  rw [factors_eq, List.length_append, List.length_map]
  congr 1
  have : ∀ l : List K, (l.flatMap fun k =>
      gadgetFactors τ (mapVar embSel (x k)) (mapVar embSel (y k))
        (Sum.inr (Sum.inr (k, false))) (Sum.inr (Sum.inr (k, true)))).length = 4 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons k l ih => simp [List.flatMap_cons, ih]; omega
  rw [this, Finset.length_toList, Finset.card_univ]

/-- **Support**: if every flow factor mentions at most three variables and the gadget
inputs are single variables (or constants), every factor of the compiled representation
mentions at most three variables. -/
theorem supportLE_three
    (hflow : ∀ Af ∈ flowForms, Af.numVars ≤ 3)
    (hx : ∀ k, (x k).numVars ≤ 1) (hy : ∀ k, (y k).numVars ≤ 1) :
    (compiled τ flowForms x y).SupportLE 3 := by
  intro Af hAf
  rw [factors_eq] at hAf
  rcases List.mem_append.mp hAf with h | h
  · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp h
    rw [mapVar, numVars]
    simpa [numVars] using hflow B hB
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
    have := numVars_gadgetFactors_le hk
    have hx' : (mapVar (F := F) (embSel (K := K)) (x k)).numVars ≤ 1 := by
      simpa [mapVar, numVars] using hx k
    have hy' : (mapVar (F := F) (embSel (K := K)) (y k)).numVars ≤ 1 := by
      simpa [mapVar, numVars] using hy k
    omega

end compiled

section Value

variable (τ : F) (flowForms : List (AffineForm (ι ⊕ A) F)) (x y : K → AffineForm (ι ⊕ A) F)

theorem subst_comp_embSel (u : (A ⊕ K × Bool) → Bool) :
    (Sum.elim X fun a => boolVal (u a)) ∘ (embSel (ι := ι) (A := A) (K := K))
      = (substSel (F := F) fun a => u (Sum.inl a)) := by
  funext w
  rcases w with i | a <;> rfl

/-- The product of the compiled factors at a Boolean point. -/
theorem prod_factors_eval (u : (A ⊕ K × Bool) → Bool) :
    ((compiled τ flowForms x y).factors.map fun Af =>
        Af.eval ((compiled τ flowForms x y).subst u)).prod
      = (flowForms.map fun Af => Af.eval (substSel fun a => u (Sum.inl a))).prod
        * ∏ k : K, gadgetBody τ ((x k).eval (substSel fun a => u (Sum.inl a)))
            ((y k).eval (substSel fun a => u (Sum.inl a)))
            (boolVal (u (Sum.inr (k, false)))) (boolVal (u (Sum.inr (k, true)))) := by
  have hsubst : (compiled τ flowForms x y).subst u
      = Sum.elim X fun a => boolVal (u a) := rfl
  rw [compiled.factors_eq]
  simp only [List.map_append, List.prod_append, List.map_map, Function.comp_def]
  congr 1
  · refine congrArg List.prod (List.map_congr_left fun B _ => ?_)
    rw [hsubst, eval_mapVar, subst_comp_embSel]
  · rw [List.map_flatMap]
    have hflat : ∀ l : List K, ((l.flatMap fun k =>
        (gadgetFactors τ (mapVar embSel (x k)) (mapVar embSel (y k))
          (Sum.inr (Sum.inr (k, false))) (Sum.inr (Sum.inr (k, true)))).map fun Af =>
            Af.eval ((compiled τ flowForms x y).subst u))).prod
        = (l.map fun k => gadgetBody τ ((x k).eval (substSel fun a => u (Sum.inl a)))
            ((y k).eval (substSel fun a => u (Sum.inl a)))
            (boolVal (u (Sum.inr (k, false)))) (boolVal (u (Sum.inr (k, true))))).prod := by
      intro l
      induction l with
      | nil => simp
      | cons k l ih =>
          rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]
          congr 1
          rw [prod_gadgetFactors τ _ _ _ _ _ (u (Sum.inr (k, false))) (u (Sum.inr (k, true)))
            (by rw [hsubst]; rfl) (by rw [hsubst]; rfl)]
          rw [hsubst, eval_mapVar, eval_mapVar, subst_comp_embSel]
    rw [← Finset.prod_map_toList]
    exact hflat _

/-- **The compiler identity.**  The compiled representation computes the hypercube sum, over
the selection bits only, of the product of the flow factors and of the quadratic factors
`1 + x_k y_k`. -/
theorem compiled_value {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (compiled τ flowForms x y).value
      = ∑ z : A → Bool, (flowForms.map fun Af => Af.eval (substSel z)).prod
          * ∏ k : K, (1 + (x k).eval (substSel z) * (y k).eval (substSel z)) := by
  show (∑ u : (A ⊕ K × Bool) → Bool,
      ((compiled τ flowForms x y).factors.map fun Af =>
        Af.eval ((compiled τ flowForms x y).subst u)).prod) = _
  rw [Finset.sum_congr rfl fun u _ => prod_factors_eval τ flowForms x y u]
  have hcube := sum_sumCube (M := MvPolynomial ι F)
      (g := fun (z : A → Bool) (w : K → Bool × Bool) =>
        (flowForms.map fun Af => Af.eval (substSel (ι := ι) (F := F) z)).prod
          * ∏ k : K, gadgetBody τ ((x k).eval (substSel (ι := ι) (F := F) z))
              ((y k).eval (substSel (ι := ι) (F := F) z))
              (boolVal (w k).1) (boolVal (w k).2))
  simp only [] at hcube
  rw [hcube]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [← prod_sum_flatten (fun k b e => gadgetBody τ ((x k).eval (substSel z))
    ((y k).eval (substSel z)) (boolVal b) (boolVal e))]
  exact Finset.prod_congr rfl fun k _ => fourFactor_identity hτ0 hτ1 _ _

end Value

end VNP1Char2
