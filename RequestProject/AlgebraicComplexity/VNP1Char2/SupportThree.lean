/-
# Support at most three

The support bound is **not** a statement about arbitrary algebraic branching programs: an
edge labelled `x₁ + x₂ + x₃` immediately produces an affine factor of support `4` after the
edge-selector gadget (see `RegressionTests`).  It holds under two hypotheses, both of which
the formula-generated graphs of `FormulaToDAG` satisfy:

* every vertex has total degree at most three, so every flow factor mentions at most three
  edge-selection variables;
* every edge label is a single variable or a constant, so every edge-selector gadget input
  contributes at most one variable and each of the four gadget factors mentions at most one
  original variable plus the two fresh auxiliaries.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.CompilerSize

namespace VNP1Char2

namespace PathGraph

open scoped BigOperators
open AffineForm

variable {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {F : Type*} [Field F] [CharP F 2]
variable (G : PathGraph V E) (lab : E → AffineForm ι F) (τ : F)

@[simp] theorem numVars_flowAff (v : V) :
    (flowAff (ι := ι) (F := F) G v).numVars =
      if v = G.s then (G.outEdges G.s).card
      else if v = G.t then (G.inEdges G.t).card
      else (G.inEdges v).card + (G.outEdges v).card := by
  unfold flowAff numVars
  split_ifs <;> simp [length_selTerms]

/-- Every flow factor of a graph of total degree at most three mentions at most three
edge-selection variables. -/
theorem flowForms_numVars_le_three
    (hdeg : ∀ v : V, (G.inEdges v).card + (G.outEdges v).card ≤ 3) :
    ∀ Af ∈ flowForms (ι := ι) (F := F) G, Af.numVars ≤ 3 := by
  intro Af hAf
  obtain ⟨v, rfl⟩ : ∃ v, flowAff (ι := ι) (F := F) G v = Af := by simpa [flowForms] using hAf
  rw [numVars_flowAff]
  have h := hdeg v
  have hs := hdeg G.s
  have ht := hdeg G.t
  split_ifs <;> omega

theorem numVars_gadgetX_le_one (hlab : ∀ a : E, (lab a).numVars ≤ 1) (k : G.GadgetIdx) :
    (gadgetX G lab k).numVars ≤ 1 := by
  rcases k with a | (q | q)
  · show (scaleShift 1 (mapVar Sum.inl (lab a)) 1 []).numVars ≤ 1
    simpa [numVars, mapVar, scaleShift] using hlab a
  · exact le_of_eq (numVars_varForm _)
  · exact le_of_eq (numVars_varForm _)

theorem numVars_gadgetY_le_one (k : G.GadgetIdx) :
    (gadgetY (F := F) (ι := ι) G k).numVars ≤ 1 := by
  rcases k with a | (q | q) <;> exact le_of_eq (numVars_varForm _)

/-- **(SUPPORT3)** for a bounded-degree DAG with single-variable edge labels: every affine
factor of the compiled representation mentions at most three variables. -/
theorem graphRep_supportLE_three
    (hdeg : ∀ v : V, (G.inEdges v).card + (G.outEdges v).card ≤ 3)
    (hlab : ∀ a : E, (lab a).numVars ≤ 1) :
    (graphRep G lab τ).SupportLE 3 :=
  compiled.supportLE_three τ _ _ _ (flowForms_numVars_le_three G hdeg)
    (numVars_gadgetX_le_one G lab hlab) (numVars_gadgetY_le_one G)

end PathGraph

end VNP1Char2
