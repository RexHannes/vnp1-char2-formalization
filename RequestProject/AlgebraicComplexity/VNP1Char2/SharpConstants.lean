/-
# Sharp pair count of the formula-generated DAG

The coarse bound used by the support-two compiler is `P ≤ 4|E|`, where `P` is the number of
*ordered* pairs of distinct edges sharing a head or a tail.  For the formula-generated
graphs the exact value is much smaller: pairs are created **only** by an addition gate,
which contributes two ordered out-pairs at its fresh source and two ordered in-pairs at its
fresh sink, so

```text
P = 4a          (a = number of addition gates).
```

Everything is derived from the vertex-local count

```text
pairsAt v = (deg⁻ v)² - deg⁻ v + (deg⁺ v)² - deg⁺ v,     P = ∑_v pairsAt v,
```

together with the degree invariant `GoodDeg` (no edge enters the source, none leaves the
sink), which is exactly what makes the connector edges of `mulDag` and `addDag` create no
new pair.

Consequence (`Formula.rep2_numAux_le_sharp`): the number of summed Boolean variables of the
support-two compiled representation satisfies `q ≤ 14 · size f`, the constant conjectured
in the memo.  The factor count improves to `M ≤ 34 · size f`.

The second conjectured identity of the memo, `D + B = 2a` for the number of degree-three
vertices, is **not** proved here: the number of degree-three vertices of a formula graph is
not a function of `(l, a, u)` alone.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.MainCompilerTwo

namespace VNP1Char2

open scoped BigOperators

namespace PathGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The number of ordered pair-exclusion constraints contributed by a single vertex. -/
def pairsAt (G : PathGraph V E) (v : V) : ℕ :=
  ((G.inEdges v).card * (G.inEdges v).card - (G.inEdges v).card) +
    ((G.outEdges v).card * (G.outEdges v).card - (G.outEdges v).card)

omit [DecidableEq E] in
/-- The pair count is the sum of the vertex-local pair counts. -/
theorem numPairs_eq_sum_pairsAt (G : PathGraph V E) : G.numPairs = ∑ v : V, G.pairsAt v := by
  rw [numPairs, inPairs, outPairs, Finset.card_sigma, Finset.card_sigma,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by
    rw [Finset.offDiag_card, Finset.offDiag_card]; rfl

end PathGraph

namespace LabelledDag

variable {ι F : Type} [Field F] (P Q : LabelledDag ι F)

theorem mulDag_sum_verts {M : Type*} [AddCommMonoid M] (f : (mulDag P Q).V → M) :
    (∑ v, f v) = (∑ v : P.V, f (Sum.inl v)) + ∑ v : Q.V, f (Sum.inr v) := by
  show (∑ v : P.V ⊕ Q.V, f v) = _
  rw [Fintype.sum_sum_type]

theorem addDag_sum_verts {M : Type*} [AddCommMonoid M] (f : (addDag P Q).V → M) :
    (∑ v, f v) = ((∑ v : P.V, f (Sum.inl (Sum.inl v))) + ∑ v : Q.V, f (Sum.inl (Sum.inr v)))
      + (f (Sum.inr false) + f (Sum.inr true)) := by
  show (∑ v : (P.V ⊕ Q.V) ⊕ Bool, f v) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_bool,
    add_comm (f (Sum.inr true)) (f (Sum.inr false))]

omit [Field F] in
/-- A leaf graph has a single edge, hence no pair exclusion at all. -/
theorem leafDag_numPairs (A : AffineForm ι F) : (leafDag A).G.numPairs = 0 := by
  rw [PathGraph.numPairs_eq_sum_pairsAt]
  refine Finset.sum_eq_zero fun v _ => ?_
  have hv : ((leafDag A).G.inEdges v).card ≤ 1 ∧ ((leafDag A).G.outEdges v).card ≤ 1 := by
    constructor <;> cases v <;>
      simp [PathGraph.card_inEdges, PathGraph.card_outEdges, leafDag]
  unfold PathGraph.pairsAt
  have h1 := hv.1
  have h2 := hv.2
  have e1 : ((leafDag A).G.inEdges v).card * ((leafDag A).G.inEdges v).card
      = ((leafDag A).G.inEdges v).card := by
    interval_cases h : ((leafDag A).G.inEdges v).card <;> simp
  have e2 : ((leafDag A).G.outEdges v).card * ((leafDag A).G.outEdges v).card
      = ((leafDag A).G.outEdges v).card := by
    interval_cases h : ((leafDag A).G.outEdges v).card <;> simp
  omega

/-- The multiplication connector edge creates no pair exclusion: it is the only edge leaving
the left sink and the only edge entering the right source. -/
theorem mulDag_numPairs (hP : GoodDeg P) (hQ : GoodDeg Q) :
    (mulDag P Q).G.numPairs = P.G.numPairs + Q.G.numPairs := by
  rw [PathGraph.numPairs_eq_sum_pairsAt, PathGraph.numPairs_eq_sum_pairsAt,
    PathGraph.numPairs_eq_sum_pairsAt, mulDag_sum_verts]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    unfold PathGraph.pairsAt
    rw [mulDag_card_inEdges_inl, mulDag_card_outEdges_inl]
    by_cases h : P.G.t = v
    · subst h
      rw [if_pos rfl, hP.2.1]
    · rw [if_neg h, add_zero]
  · refine Finset.sum_congr rfl fun v _ => ?_
    unfold PathGraph.pairsAt
    rw [mulDag_card_inEdges_inr, mulDag_card_outEdges_inr]
    by_cases h : Q.G.s = v
    · subst h
      rw [if_pos rfl, hQ.1]
    · rw [if_neg h, add_zero]

/-- An addition gate creates exactly four ordered pair exclusions: two at its fresh source
(out-degree two) and two at its fresh sink (in-degree two).  The four connector edges create
no other pair. -/
theorem addDag_numPairs (hP : GoodDeg P) (hQ : GoodDeg Q) :
    (addDag P Q).G.numPairs = P.G.numPairs + Q.G.numPairs + 4 := by
  rw [PathGraph.numPairs_eq_sum_pairsAt, PathGraph.numPairs_eq_sum_pairsAt,
    PathGraph.numPairs_eq_sum_pairsAt, addDag_sum_verts]
  have hsrc : (addDag P Q).G.pairsAt (Sum.inr false) = 2 := by
    unfold PathGraph.pairsAt
    rw [addDag_card_inEdges_src, addDag_card_outEdges_src]
  have htgt : (addDag P Q).G.pairsAt (Sum.inr true) = 2 := by
    unfold PathGraph.pairsAt
    rw [addDag_card_inEdges_tgt, addDag_card_outEdges_tgt]
  rw [hsrc, htgt]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    unfold PathGraph.pairsAt
    rw [addDag_card_inEdges_inll, addDag_card_outEdges_inll]
    by_cases h1 : P.G.s = v
    · subst h1
      rw [if_pos rfl, hP.1, if_neg (Ne.symm P.G.hst), add_zero]
    · rw [if_neg h1, add_zero]
      by_cases h2 : P.G.t = v
      · subst h2
        rw [if_pos rfl, hP.2.1]
      · rw [if_neg h2, add_zero]
  · refine Finset.sum_congr rfl fun v _ => ?_
    unfold PathGraph.pairsAt
    rw [addDag_card_inEdges_inlr, addDag_card_outEdges_inlr]
    by_cases h1 : Q.G.s = v
    · subst h1
      rw [if_pos rfl, hQ.1, if_neg (Ne.symm Q.G.hst), add_zero]
    · rw [if_neg h1, add_zero]
      by_cases h2 : Q.G.t = v
      · subst h2
        rw [if_pos rfl, hQ.2.1]
      · rw [if_neg h2, add_zero]

end LabelledDag

namespace Formula

variable {ι F : Type} [Field F]

/-- **The sharp pair count:** `P = 4a`.  Pair exclusions are created only by addition
gates. -/
theorem toDag_numPairs (f : Formula ι F) : f.toDag.G.numPairs = 4 * f.addGates := by
  induction f with
  | var i => exact LabelledDag.leafDag_numPairs _
  | const c => exact LabelledDag.leafDag_numPairs _
  | add p q ihp ihq =>
      show (addDag p.toDag q.toDag).G.numPairs = _
      rw [LabelledDag.addDag_numPairs _ _ p.toDag_goodDeg q.toDag_goodDeg, ihp, ihq]
      show _ = 4 * (p.addGates + q.addGates + 1)
      ring
  | mul p q ihp ihq =>
      show (mulDag p.toDag q.toDag).G.numPairs = _
      rw [LabelledDag.mulDag_numPairs _ _ p.toDag_goodDeg q.toDag_goodDeg, ihp, ihq]
      show _ = 4 * (p.addGates + q.addGates)
      ring

variable [CharP F 2]

omit [CharP F 2] in
/-- **Sharp size accounting, summed Boolean variables:** with `P = 4a`,
`q = 2|E| + D + P ≤ 14 · size f`, the constant conjectured in the memo. -/
theorem rep2_numAux_le_sharp (f : Formula ι F) (τ : F) : (f.rep2 τ).numAux ≤ 14 * f.size := by
  rw [rep2, PathGraph.graphRep2_numAux]
  have hP := f.toDag_numPairs
  have hD : (f.toDag.G.ternVerts).card ≤ Fintype.card f.toDag.V :=
    le_trans (Finset.card_le_univ _) (le_of_eq (Finset.card_univ))
  rw [f.toDag_card_E, hP]
  rw [f.toDag_card_V] at hD
  have hs : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

omit [CharP F 2] in
/-- **Sharp size accounting, affine factors:** with `P = 4a`,
`M = |V| + 4D + 3(|E| + P) ≤ 34 · size f`. -/
theorem rep2_numFactors_le_sharp (f : Formula ι F) (τ : F) :
    (f.rep2 τ).numFactors ≤ 34 * f.size := by
  rw [rep2, PathGraph.graphRep2_numFactors]
  have hP := f.toDag_numPairs
  have hD : (f.toDag.G.ternVerts).card ≤ Fintype.card f.toDag.V :=
    le_trans (Finset.card_le_univ _) (le_of_eq (Finset.card_univ))
  rw [f.toDag_card_E, hP]
  rw [f.toDag_card_V] at hD ⊢
  have hs : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

/-- **The main finite support-two compiler theorem, with the sharp constants.** -/
theorem has_supportTwo_representation_sharp (f : Formula ι F) {τ : F}
    (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    ∃ R : AffineHypercubeRep ι F,
      R.Represents f.eval ∧ R.SupportLE 2 ∧
        R.numAux ≤ 14 * f.size ∧ R.numFactors ≤ 34 * f.size :=
  ⟨f.rep2 τ, f.rep2_value hτ0 hτ1, f.rep2_supportLE_two τ, f.rep2_numAux_le_sharp τ,
    f.rep2_numFactors_le_sharp τ⟩

end Formula

end VNP1Char2
