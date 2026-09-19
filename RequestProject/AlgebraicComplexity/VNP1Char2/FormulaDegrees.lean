/-
# Degrees, labels and sizes of the formula-generated DAG

This file proves the structural invariants of the graphs built in `FormulaToDAG`:

* the *degree invariant* `GoodDeg`: no selected-capable edge enters the source, none leaves
  the sink, the source has out-degree at most two, the sink in-degree at most two, and
  every vertex has total degree at most three;
* every edge label is a single variable or a field constant (`numVars ≤ 1`);
* the exact vertex and edge counts `|V| = 2l + 2a`, `|E| = l + 4a + u`;
* the value of the formula-generated DAG is the polynomial of the formula.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.FormulaToDAG

namespace VNP1Char2

open scoped BigOperators
open AffineForm MvPolynomial

namespace PathGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem card_inEdges (G : PathGraph V E) (v : V) :
    (G.inEdges v).card = ∑ a : E, if G.tgt a = v then 1 else 0 := by
  rw [inEdges, Finset.card_filter]

theorem card_outEdges (G : PathGraph V E) (v : V) :
    (G.outEdges v).card = ∑ a : E, if G.src a = v then 1 else 0 := by
  rw [outEdges, Finset.card_filter]

end PathGraph

namespace LabelledDag

variable {ι F : Type} [Field F] (P Q : LabelledDag ι F)

/-! ### Degrees of the product graph -/

theorem mulDag_card_inEdges_inl (v : P.V) :
    ((mulDag P Q).G.inEdges (Sum.inl v)).card = (P.G.inEdges v).card := by
  rw [PathGraph.card_inEdges, PathGraph.card_inEdges, mulDag_sum_edges (M := ℕ)]
  simp

theorem mulDag_card_outEdges_inl (v : P.V) :
    ((mulDag P Q).G.outEdges (Sum.inl v)).card
      = (P.G.outEdges v).card + (if P.G.t = v then 1 else 0) := by
  rw [PathGraph.card_outEdges, PathGraph.card_outEdges, mulDag_sum_edges (M := ℕ)]
  simp

theorem mulDag_card_inEdges_inr (v : Q.V) :
    ((mulDag P Q).G.inEdges (Sum.inr v)).card
      = (Q.G.inEdges v).card + (if Q.G.s = v then 1 else 0) := by
  rw [PathGraph.card_inEdges, PathGraph.card_inEdges, mulDag_sum_edges (M := ℕ)]
  simp

theorem mulDag_card_outEdges_inr (v : Q.V) :
    ((mulDag P Q).G.outEdges (Sum.inr v)).card = (Q.G.outEdges v).card := by
  rw [PathGraph.card_outEdges, PathGraph.card_outEdges, mulDag_sum_edges (M := ℕ)]
  simp

/-! ### Degrees of the sum graph -/

theorem addDag_card_inEdges_inll (v : P.V) :
    ((addDag P Q).G.inEdges (Sum.inl (Sum.inl v))).card
      = (P.G.inEdges v).card + (if P.G.s = v then 1 else 0) := by
  rw [PathGraph.card_inEdges, PathGraph.card_inEdges, addDag_sum_edges (M := ℕ)]
  simp

theorem addDag_card_outEdges_inll (v : P.V) :
    ((addDag P Q).G.outEdges (Sum.inl (Sum.inl v))).card
      = (P.G.outEdges v).card + (if P.G.t = v then 1 else 0) := by
  rw [PathGraph.card_outEdges, PathGraph.card_outEdges, addDag_sum_edges (M := ℕ)]
  simp

theorem addDag_card_inEdges_inlr (v : Q.V) :
    ((addDag P Q).G.inEdges (Sum.inl (Sum.inr v))).card
      = (Q.G.inEdges v).card + (if Q.G.s = v then 1 else 0) := by
  rw [PathGraph.card_inEdges, PathGraph.card_inEdges, addDag_sum_edges (M := ℕ)]
  simp

theorem addDag_card_outEdges_inlr (v : Q.V) :
    ((addDag P Q).G.outEdges (Sum.inl (Sum.inr v))).card
      = (Q.G.outEdges v).card + (if Q.G.t = v then 1 else 0) := by
  rw [PathGraph.card_outEdges, PathGraph.card_outEdges, addDag_sum_edges (M := ℕ)]
  simp

theorem addDag_card_inEdges_src : ((addDag P Q).G.inEdges (Sum.inr false)).card = 0 := by
  rw [PathGraph.card_inEdges, addDag_sum_edges (M := ℕ)]
  simp

theorem addDag_card_outEdges_src : ((addDag P Q).G.outEdges (Sum.inr false)).card = 2 := by
  rw [PathGraph.card_outEdges, addDag_sum_edges (M := ℕ)]
  simp

theorem addDag_card_inEdges_tgt : ((addDag P Q).G.inEdges (Sum.inr true)).card = 2 := by
  rw [PathGraph.card_inEdges, addDag_sum_edges (M := ℕ)]
  simp

theorem addDag_card_outEdges_tgt : ((addDag P Q).G.outEdges (Sum.inr true)).card = 0 := by
  rw [PathGraph.card_outEdges, addDag_sum_edges (M := ℕ)]
  simp

/-! ### The degree invariant -/

/-- The degree invariant maintained by the compilation of a formula: the source has no
incoming edge and out-degree at most two, the sink has no outgoing edge and in-degree at
most two, and every vertex has total degree at most three. -/
def GoodDeg (D : LabelledDag ι F) : Prop :=
  (D.G.inEdges D.G.s).card = 0 ∧ (D.G.outEdges D.G.t).card = 0 ∧
  (D.G.outEdges D.G.s).card ≤ 2 ∧ (D.G.inEdges D.G.t).card ≤ 2 ∧
  ∀ v, (D.G.inEdges v).card + (D.G.outEdges v).card ≤ 3

theorem leafDag_goodDeg (A : AffineForm ι F) : GoodDeg (leafDag A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [PathGraph.card_inEdges, leafDag_sum_edges, leafDag]
  · simp [PathGraph.card_outEdges, leafDag_sum_edges, leafDag]
  · simp [PathGraph.card_outEdges, leafDag_sum_edges, leafDag]
  · simp [PathGraph.card_inEdges, leafDag_sum_edges, leafDag]
  · intro v
    cases v <;>
      simp [PathGraph.card_inEdges, PathGraph.card_outEdges, leafDag_sum_edges, leafDag]

theorem mulDag_goodDeg (hP : GoodDeg P) (hQ : GoodDeg Q) : GoodDeg (mulDag P Q) := by
  obtain ⟨hPs, hPt, hPs2, hPt2, hPall⟩ := hP
  obtain ⟨hQs, hQt, hQs2, hQt2, hQall⟩ := hQ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ((mulDag P Q).G.inEdges (Sum.inl P.G.s)).card = 0
    rw [mulDag_card_inEdges_inl]; exact hPs
  · show ((mulDag P Q).G.outEdges (Sum.inr Q.G.t)).card = 0
    rw [mulDag_card_outEdges_inr]; exact hQt
  · show ((mulDag P Q).G.outEdges (Sum.inl P.G.s)).card ≤ 2
    rw [mulDag_card_outEdges_inl, if_neg (Ne.symm P.G.hst)]
    simpa using hPs2
  · show ((mulDag P Q).G.inEdges (Sum.inr Q.G.t)).card ≤ 2
    rw [mulDag_card_inEdges_inr, if_neg Q.G.hst]
    simpa using hQt2
  · rintro (v | v)
    · rw [mulDag_card_inEdges_inl, mulDag_card_outEdges_inl]
      by_cases h : P.G.t = v
      · subst h
        rw [if_pos rfl]
        have := hPall P.G.t
        omega
      · rw [if_neg h]
        have := hPall v
        omega
    · rw [mulDag_card_inEdges_inr, mulDag_card_outEdges_inr]
      by_cases h : Q.G.s = v
      · subst h
        rw [if_pos rfl]
        have := hQall Q.G.s
        omega
      · rw [if_neg h]
        have := hQall v
        omega

theorem addDag_goodDeg (hP : GoodDeg P) (hQ : GoodDeg Q) : GoodDeg (addDag P Q) := by
  obtain ⟨hPs, hPt, hPs2, hPt2, hPall⟩ := hP
  obtain ⟨hQs, hQt, hQs2, hQt2, hQall⟩ := hQ
  refine ⟨addDag_card_inEdges_src P Q, addDag_card_outEdges_tgt P Q,
    le_of_eq (addDag_card_outEdges_src P Q), le_of_eq (addDag_card_inEdges_tgt P Q), ?_⟩
  rintro ((v | v) | b)
  · rw [addDag_card_inEdges_inll, addDag_card_outEdges_inll]
    by_cases h : P.G.s = v
    · subst h
      rw [if_pos rfl, if_neg (Ne.symm P.G.hst)]
      have := hPall P.G.s
      omega
    · rw [if_neg h]
      by_cases h' : P.G.t = v
      · subst h'
        rw [if_pos rfl]
        have := hPall P.G.t
        omega
      · rw [if_neg h']
        have := hPall v
        omega
  · rw [addDag_card_inEdges_inlr, addDag_card_outEdges_inlr]
    by_cases h : Q.G.s = v
    · subst h
      rw [if_pos rfl, if_neg (Ne.symm Q.G.hst)]
      have := hQall Q.G.s
      omega
    · rw [if_neg h]
      by_cases h' : Q.G.t = v
      · subst h'
        rw [if_pos rfl]
        have := hQall Q.G.t
        omega
      · rw [if_neg h']
        have := hQall v
        omega
  · cases b
    · rw [addDag_card_inEdges_src, addDag_card_outEdges_src]; omega
    · rw [addDag_card_inEdges_tgt, addDag_card_outEdges_tgt]; omega

/-! ### Labels -/

/-- Every edge label mentions at most one variable. -/
def GoodLab (D : LabelledDag ι F) : Prop := ∀ a, (D.lab a).numVars ≤ 1

theorem leafDag_goodLab {A : AffineForm ι F} (h : A.numVars ≤ 1) : GoodLab (leafDag A) :=
  fun _ => h

theorem mulDag_goodLab (hP : GoodLab P) (hQ : GoodLab Q) : GoodLab (mulDag P Q) := by
  rintro ((a | a) | u)
  · exact hP a
  · exact hQ a
  · exact Nat.zero_le _

theorem addDag_goodLab (hP : GoodLab P) (hQ : GoodLab Q) : GoodLab (addDag P Q) := by
  rintro ((a | a) | c)
  · exact hP a
  · exact hQ a
  · exact Nat.zero_le _

/-! ### Cardinalities -/

theorem leafDag_card_V (A : AffineForm ι F) : Fintype.card (leafDag A).V = 2 := rfl
theorem leafDag_card_E (A : AffineForm ι F) : Fintype.card (leafDag A).E = 1 := rfl

theorem mulDag_card_V :
    Fintype.card (mulDag P Q).V = Fintype.card P.V + Fintype.card Q.V := by
  show Fintype.card (P.V ⊕ Q.V) = _
  simp [Fintype.card_sum]

theorem mulDag_card_E :
    Fintype.card (mulDag P Q).E = Fintype.card P.E + Fintype.card Q.E + 1 := by
  show Fintype.card ((P.E ⊕ Q.E) ⊕ Unit) = _
  simp [Fintype.card_sum]

theorem addDag_card_V :
    Fintype.card (addDag P Q).V = Fintype.card P.V + Fintype.card Q.V + 2 := by
  show Fintype.card ((P.V ⊕ Q.V) ⊕ Bool) = _
  simp [Fintype.card_sum]

theorem addDag_card_E :
    Fintype.card (addDag P Q).E = Fintype.card P.E + Fintype.card Q.E + 4 := by
  show Fintype.card ((P.E ⊕ Q.E) ⊕ AddConn) = _
  simp [Fintype.card_sum, Fintype.card_prod]

end LabelledDag

namespace Formula

variable {ι F : Type} [Field F]

/-- **The formula-generated DAG computes the formula's polynomial.** -/
theorem toDag_value (f : Formula ι F) : f.toDag.value = f.eval := by
  induction f with
  | var i =>
      rw [toDag, eval, LabelledDag.leafDag_value]
      simp [AffineForm.eval_varForm]
  | const c =>
      rw [toDag, eval, LabelledDag.leafDag_value]
      simp [AffineForm.eval, MvPolynomial.algebraMap_eq]
  | add p q ihp ihq => rw [toDag, eval, LabelledDag.addDag_value, ihp, ihq]
  | mul p q ihp ihq => rw [toDag, eval, LabelledDag.mulDag_value, ihp, ihq]

/-- **The formula-generated DAG has total degree at most three at every vertex.** -/
theorem toDag_goodDeg (f : Formula ι F) : LabelledDag.GoodDeg f.toDag := by
  induction f with
  | var i => exact LabelledDag.leafDag_goodDeg _
  | const c => exact LabelledDag.leafDag_goodDeg _
  | add p q ihp ihq => exact LabelledDag.addDag_goodDeg _ _ ihp ihq
  | mul p q ihp ihq => exact LabelledDag.mulDag_goodDeg _ _ ihp ihq

/-- **Every edge label of the formula-generated DAG is a variable or a constant.** -/
theorem toDag_goodLab (f : Formula ι F) : LabelledDag.GoodLab f.toDag := by
  induction f with
  | var i => exact LabelledDag.leafDag_goodLab (le_of_eq (numVars_varForm i))
  | const c => exact LabelledDag.leafDag_goodLab (by simp [AffineForm.numVars])
  | add p q ihp ihq => exact LabelledDag.addDag_goodLab _ _ ihp ihq
  | mul p q ihp ihq => exact LabelledDag.mulDag_goodLab _ _ ihp ihq

/-- **Vertex count:** `|V| = 2l + 2a`. -/
theorem toDag_card_V (f : Formula ι F) :
    Fintype.card f.toDag.V = 2 * f.leaves + 2 * f.addGates := by
  induction f with
  | var i => rw [toDag, LabelledDag.leafDag_card_V]; rfl
  | const c => rw [toDag, LabelledDag.leafDag_card_V]; rfl
  | add p q ihp ihq =>
      rw [toDag, LabelledDag.addDag_card_V, ihp, ihq]
      show _ = 2 * (p.leaves + q.leaves) + 2 * (p.addGates + q.addGates + 1)
      ring
  | mul p q ihp ihq =>
      rw [toDag, LabelledDag.mulDag_card_V, ihp, ihq]
      show _ = 2 * (p.leaves + q.leaves) + 2 * (p.addGates + q.addGates)
      ring

/-- **Edge count:** `|E| = l + 4a + u`. -/
theorem toDag_card_E (f : Formula ι F) :
    Fintype.card f.toDag.E = f.leaves + 4 * f.addGates + f.mulGates := by
  induction f with
  | var i => rw [toDag, LabelledDag.leafDag_card_E]; rfl
  | const c => rw [toDag, LabelledDag.leafDag_card_E]; rfl
  | add p q ihp ihq =>
      rw [toDag, LabelledDag.addDag_card_E, ihp, ihq]
      show _ = (p.leaves + q.leaves) + 4 * (p.addGates + q.addGates + 1)
        + (p.mulGates + q.mulGates)
      ring
  | mul p q ihp ihq =>
      rw [toDag, LabelledDag.mulDag_card_E, ihp, ihq]
      show _ = (p.leaves + q.leaves) + 4 * (p.addGates + q.addGates)
        + (p.mulGates + q.mulGates + 1)
      ring

end Formula

end VNP1Char2
