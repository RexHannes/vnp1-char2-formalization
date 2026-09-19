/-
# Size accounting for the DAG compiler

For a labelled DAG `G` with `|E|` edges, `|V|` vertices and `P` ordered pair-exclusion
constraints (`P = |inPairs| + |outPairs|`, the number of *ordered* pairs of distinct edges
sharing a head or a tail), the compiled representation uses

* `q = 3|E| + 2P` summed Boolean variables:
  `|E|` edge-selection bits, `2|E|` edge-selector gadget auxiliaries and `2P` pair-gadget
  auxiliaries;
* `M = |V| + 4(|E| + P)` affine factors:
  one flow factor per vertex and four affine factors per gadget occurrence.

Both counts are derived from the generic compiler counts `compiled.numAux_eq`
and `compiled.numFactors_eq`, instantiated at the graph data.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.GraphCompiler

namespace VNP1Char2

namespace PathGraph

open scoped BigOperators
open AffineForm

variable {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {F : Type*} [Field F] [CharP F 2]
variable (G : PathGraph V E) (lab : E → AffineForm ι F) (τ : F)

/-- The number of (ordered) pair-exclusion constraints of the graph. -/
def numPairs : ℕ := G.inPairs.card + G.outPairs.card

theorem card_gadgetIdx :
    Fintype.card G.GadgetIdx = Fintype.card E + G.numPairs := by
  simp [GadgetIdx, Fintype.card_sum, Fintype.card_coe, numPairs]

theorem length_flowForms : (flowForms (ι := ι) (F := F) G).length = Fintype.card V := by
  simp [flowForms]

/-- **Size accounting, summed Boolean variables:** `q = 3|E| + 2P`. -/
theorem graphRep_numAux :
    (graphRep G lab τ).numAux = 3 * Fintype.card E + 2 * G.numPairs := by
  rw [graphRep, compiled.numAux_eq, card_gadgetIdx]
  ring

/-- **Size accounting, affine factors:** `M = |V| + 4(|E| + P)`. -/
theorem graphRep_numFactors :
    (graphRep G lab τ).numFactors = Fintype.card V + 4 * (Fintype.card E + G.numPairs) := by
  rw [graphRep, compiled.numFactors_eq, length_flowForms, card_gadgetIdx]

end PathGraph

end VNP1Char2
