/-
# Compiling a labelled DAG into an affine-product hypercube representation

Putting the two halves together:

* `PathPolynomial.abp_identity`: the graph polynomial is the hypercube sum, over the edge
  selections `z`, of `V_G(z) ∏_a E_a(z, X)`;
* `Compiler.compiled_value`: a product of flow factors and of quadratic factors
  `1 + x_k y_k` is compiled into an affine-product hypercube representation with two fresh
  auxiliaries per quadratic factor.

Every quadratic factor of `V_G(z) ∏_a E_a(z, X)` is of the form `1 + x y`:

* the pair exclusion `1 + z_a z_b` at a vertex, with `x = z_a`, `y = z_b`;
* the edge selector `E_a = 1 + (ℓ_a + 1) z_a`, with `x = ℓ_a + 1`, `y = z_a`.

The flow factors are already affine in the selection variables.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.Compiler
import RequestProject.AlgebraicComplexity.VNP1Char2.PathPolynomial

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace VNP1Char2

namespace PathGraph

open scoped BigOperators
open AffineForm MvPolynomial

variable {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {F : Type*} [Field F] [CharP F 2]
variable (G : PathGraph V E) (lab : E → AffineForm ι F)

/-- Ordered pairs of distinct edges sharing a head. -/
def inPairs : Finset ((_ : V) × (E × E)) := Finset.univ.sigma fun v => (G.inEdges v).offDiag

/-- Ordered pairs of distinct edges sharing a tail. -/
def outPairs : Finset ((_ : V) × (E × E)) := Finset.univ.sigma fun v => (G.outEdges v).offDiag

/-- The index type of gadget occurrences: one per edge (the edge-weight selector) and one
per pair exclusion. -/
abbrev GadgetIdx : Type := E ⊕ ({q // q ∈ G.inPairs} ⊕ {q // q ∈ G.outPairs})

/-- The linear terms `∑_{a ∈ S} z_a`. -/
noncomputable def selTerms (S : Finset E) : List (F × (ι ⊕ E)) :=
  S.toList.map fun a => (1, Sum.inr a)

@[simp] theorem length_selTerms (S : Finset E) :
    (selTerms (F := F) (ι := ι) S).length = S.card := by
  simp [selTerms]

/-- The flow factor at `v` as an affine form in the edge-selection variables. -/
noncomputable def flowAff (v : V) : AffineForm (ι ⊕ E) F :=
  if v = G.s then ⟨0, selTerms (G.outEdges G.s)⟩
  else if v = G.t then ⟨0, selTerms (G.inEdges G.t)⟩
  else ⟨1, selTerms (G.inEdges v) ++ selTerms (G.outEdges v)⟩

/-- The list of flow factors, one per vertex. -/
noncomputable def flowForms : List (AffineForm (ι ⊕ E) F) :=
  (Finset.univ : Finset V).toList.map (flowAff (ι := ι) (F := F) G)

/-- First input of each gadget: `ℓ_a + 1` for an edge selector, `z_a` for a pair
exclusion. -/
noncomputable def gadgetX : G.GadgetIdx → AffineForm (ι ⊕ E) F
  | Sum.inl a => scaleShift 1 (mapVar Sum.inl (lab a)) 1 []
  | Sum.inr (Sum.inl q) => varForm (Sum.inr q.1.2.1)
  | Sum.inr (Sum.inr q) => varForm (Sum.inr q.1.2.1)

/-- Second input of each gadget: `z_a` for an edge selector, `z_b` for a pair exclusion. -/
def gadgetY : G.GadgetIdx → AffineForm (ι ⊕ E) F
  | Sum.inl a => varForm (Sum.inr a)
  | Sum.inr (Sum.inl q) => varForm (Sum.inr q.1.2.2)
  | Sum.inr (Sum.inr q) => varForm (Sum.inr q.1.2.2)

/-- The polynomial computed by the graph, with the affine edge labels evaluated at the
original indeterminates. -/
noncomputable def labelPoly (a : E) : MvPolynomial ι F := (lab a).eval (X : ι → MvPolynomial ι F)

/-- The compiled representation of the graph polynomial. -/
noncomputable def graphRep (τ : F) : AffineHypercubeRep ι F :=
  compiled τ (flowForms G) (gadgetX G lab) (gadgetY G)

section Eval

variable (z : E → Bool)

theorem substSel_inr (a : E) :
    (substSel (ι := ι) (F := F) z) (Sum.inr a) = (boolVal (z a) : MvPolynomial ι F) := rfl

theorem substSel_inl : (substSel (ι := ι) (F := F) z) ∘ Sum.inl = (X : ι → MvPolynomial ι F) :=
  rfl

theorem sum_selTerms (S : Finset E) :
    ((selTerms (F := F) (ι := ι) S).map fun p =>
        algebraMap F (MvPolynomial ι F) p.1 * (substSel (F := F) z) p.2).sum
      = algebraMap F (MvPolynomial ι F) (∑ a ∈ S, (boolVal (z a) : F)) := by
  rw [selTerms, List.map_map]
  have hfun : ((fun p : F × (ι ⊕ E) => algebraMap F (MvPolynomial ι F) p.1 *
      (substSel (F := F) z) p.2) ∘ fun a => ((1 : F), (Sum.inr a : ι ⊕ E)))
      = fun a => algebraMap F (MvPolynomial ι F) (boolVal (z a)) := by
    funext a
    simp only [Function.comp_apply, map_one, one_mul, substSel_inr]
    cases z a <;> simp [boolVal]
  rw [hfun, Finset.sum_map_toList, map_sum]

/-- The affine flow factor evaluates to the flow factor of the selector polynomial. -/
theorem eval_flowAff (v : V) :
    (flowAff (ι := ι) (F := F) G v).eval (substSel (F := F) z)
      = algebraMap F (MvPolynomial ι F) (flowFactor F G z v) := by
  unfold flowAff flowFactor AffineForm.eval
  split_ifs
  · rw [sum_selTerms]; simp
  · rw [sum_selTerms]; simp
  · simp only [List.map_append, List.sum_append]
    rw [sum_selTerms, sum_selTerms]
    simp [map_add]

/-- The edge-selector gadget reproduces `E_a(z, X)`. -/
theorem gadget_eval_inl (a : E) :
    1 + (gadgetX G lab (Sum.inl a)).eval (substSel (F := F) z)
        * (gadgetY (F := F) G (Sum.inl a)).eval (substSel (F := F) z)
      = edgeSel (labelPoly lab) z a := by
  have hx : (gadgetX G lab (Sum.inl a)).eval (substSel (F := F) z) = labelPoly lab a + 1 := by
    show (scaleShift 1 (mapVar Sum.inl (lab a)) 1 []).eval (substSel (F := F) z) = _
    rw [eval_scaleShift, eval_mapVar, substSel_inl]
    simp [labelPoly]
  rw [hx, edgeSel]
  show _ = 1 + boolVal (z a) * (labelPoly lab a + 1)
  simp only [gadgetY, eval_varForm, substSel_inr]
  ring

/-- The pair-exclusion gadgets reproduce `1 + z_a z_b`. -/
theorem gadget_eval_inr_inl (q : {q // q ∈ G.inPairs}) :
    1 + (gadgetX G lab (Sum.inr (Sum.inl q))).eval (substSel (F := F) z)
        * (gadgetY (F := F) G (Sum.inr (Sum.inl q))).eval (substSel (F := F) z)
      = 1 + (boolVal (z q.1.2.1) : MvPolynomial ι F) * boolVal (z q.1.2.2) := by
  show 1 + (varForm (Sum.inr q.1.2.1)).eval (substSel (F := F) z)
      * (varForm (Sum.inr q.1.2.2)).eval (substSel (F := F) z) = _
  simp only [eval_varForm, substSel_inr]

theorem gadget_eval_inr_inr (q : {q // q ∈ G.outPairs}) :
    1 + (gadgetX G lab (Sum.inr (Sum.inr q))).eval (substSel (F := F) z)
        * (gadgetY (F := F) G (Sum.inr (Sum.inr q))).eval (substSel (F := F) z)
      = 1 + (boolVal (z q.1.2.1) : MvPolynomial ι F) * boolVal (z q.1.2.2) := by
  show 1 + (varForm (Sum.inr q.1.2.1)).eval (substSel (F := F) z)
      * (varForm (Sum.inr q.1.2.2)).eval (substSel (F := F) z) = _
  simp only [eval_varForm, substSel_inr]

end Eval

section Main

variable (z : E → Bool)

theorem algebraMap_boolVal (b : Bool) :
    algebraMap F (MvPolynomial ι F) (boolVal b) = boolVal b := by
  cases b <;> simp

/-- The product of the affine flow factors is the flow part of the selector polynomial. -/
theorem prod_flowForms :
    (((flowForms (ι := ι) (F := F) G)).map fun Af =>
        Af.eval (substSel (F := F) z)).prod
      = algebraMap F (MvPolynomial ι F) (∏ v : V, flowFactor F G z v) := by
  rw [flowForms, List.map_map, map_prod]
  rw [← Finset.prod_map_toList]
  exact congrArg List.prod (List.map_congr_left fun v _ => eval_flowAff G z v)

/-- The pair-exclusion gadgets over a sigma-indexed finset of vertex-local pairs. -/
theorem prod_pairs (S : V → Finset E) :
    (∏ q : {q : (_ : V) × (E × E) // q ∈ Finset.univ.sigma fun v => (S v).offDiag},
        (1 + (boolVal (z q.1.2.1) : MvPolynomial ι F) * boolVal (z q.1.2.2)))
      = algebraMap F (MvPolynomial ι F) (∏ v : V, pairFactors F z (S v)) := by
  rw [Finset.prod_coe_sort (Finset.univ.sigma fun v => (S v).offDiag)
    (fun q => (1 + (boolVal (z q.2.1) : MvPolynomial ι F) * boolVal (z q.2.2)))]
  rw [Finset.prod_sigma, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [pairFactors, map_prod]
  exact Finset.prod_congr rfl fun p _ => by
    rw [map_add, map_one, map_mul, algebraMap_boolVal, algebraMap_boolVal]

theorem prod_inPairs :
    (∏ q : {q // q ∈ G.inPairs},
        (1 + (boolVal (z q.1.2.1) : MvPolynomial ι F) * boolVal (z q.1.2.2)))
      = algebraMap F (MvPolynomial ι F) (∏ v : V, pairFactors F z (G.inEdges v)) :=
  prod_pairs (ι := ι) z fun v => G.inEdges v

theorem prod_outPairs :
    (∏ q : {q // q ∈ G.outPairs},
        (1 + (boolVal (z q.1.2.1) : MvPolynomial ι F) * boolVal (z q.1.2.2)))
      = algebraMap F (MvPolynomial ι F) (∏ v : V, pairFactors F z (G.outEdges v)) :=
  prod_pairs (ι := ι) z fun v => G.outEdges v

/-- The product of the quadratic gadget bodies is the edge-weight selector product times
the pair-exclusion part of the selector polynomial. -/
theorem prod_gadgetBodies :
    (∏ k : G.GadgetIdx, (1 + (gadgetX G lab k).eval (substSel (F := F) z)
        * (gadgetY (F := F) G k).eval (substSel (F := F) z)))
      = (∏ a : E, edgeSel (labelPoly lab) z a)
        * algebraMap F (MvPolynomial ι F)
            (∏ v : V, (pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  congr 1
  · exact Finset.prod_congr rfl fun a _ => gadget_eval_inl G lab z a
  · rw [Finset.prod_congr rfl fun q _ => gadget_eval_inr_inl G lab z q,
      Finset.prod_congr rfl fun q _ => gadget_eval_inr_inr G lab z q]
    rw [show (∏ v : V, (pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v)))
        = (∏ v : V, pairFactors F z (G.inEdges v)) * ∏ v : V, pairFactors F z (G.outEdges v) from
      Finset.prod_mul_distrib, map_mul]
    rw [prod_inPairs (ι := ι) G z, prod_outPairs (ι := ι) G z]

/-- **The DAG compiler theorem.**  For a labelled DAG whose edge labels are affine forms,
the compiled affine-product hypercube representation computes exactly the graph
polynomial `val G ℓ`. -/
theorem graphRep_value {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (graphRep G lab τ).value = val G (labelPoly lab) := by
  rw [graphRep, compiled_value _ _ _ hτ0 hτ1, ← abp_identity (M := MvPolynomial ι F) G F
    (labelPoly lab)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [prod_flowForms G z, prod_gadgetBodies G lab z, selectorVal, map_mul]
  ring

end Main

end PathGraph

end VNP1Char2
