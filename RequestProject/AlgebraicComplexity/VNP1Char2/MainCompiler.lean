/-
# The main finite compiler theorem

Putting everything together: over a field of characteristic two containing an element
`τ ∉ {0, 1}`, every binary division-free arithmetic formula `f` is compiled into a finite
affine-product Boolean-hypercube representation

```
f(X) = ∑_{u ∈ {0,1}^q} ∏_{j=1}^{M} A_j(X, u)
```

with `q, M = O(size f)` and every affine factor `A_j` of variable support at most three.

The chain of results used is:

* `Formula.toDag_value` : the formula-generated DAG computes `f`;
* `PathGraph.graphRep_value` : the compiled representation computes the graph polynomial;
* `PathGraph.graphRep_supportLE_three` : with bounded degrees and one-variable labels, all
  the affine factors have support at most three;
* `PathGraph.graphRep_numAux` / `graphRep_numFactors` : the exact size accounting,
  combined with `numPairs_le` and the exact vertex/edge counts of the formula graph.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.FormulaDegrees

namespace VNP1Char2

open scoped BigOperators
open AffineForm MvPolynomial

namespace PathGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : PathGraph V E)

theorem sum_card_inEdges : (∑ v : V, (G.inEdges v).card) = Fintype.card E := by
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise (f := G.tgt) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun v _ => rfl

theorem sum_card_outEdges : (∑ v : V, (G.outEdges v).card) = Fintype.card E := by
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise (f := G.src) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun v _ => rfl

/-- With total degree at most three at every vertex, the number of ordered pair-exclusion
constraints is at most `4|E|`. -/
theorem numPairs_le (hdeg : ∀ v : V, (G.inEdges v).card + (G.outEdges v).card ≤ 3) :
    G.numPairs ≤ 4 * Fintype.card E := by
  have hin : G.inPairs.card ≤ 2 * Fintype.card E := by
    rw [inPairs, Finset.card_sigma, ← sum_card_inEdges G, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [Finset.offDiag_card]
    have := hdeg v
    have h3 : (G.inEdges v).card ≤ 3 := by omega
    have hmul : (G.inEdges v).card * (G.inEdges v).card ≤ 3 * (G.inEdges v).card :=
      Nat.mul_le_mul h3 (le_refl _)
    have hsub := Nat.sub_le_sub_right hmul (G.inEdges v).card
    omega
  have hout : G.outPairs.card ≤ 2 * Fintype.card E := by
    rw [outPairs, Finset.card_sigma, ← sum_card_outEdges G, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [Finset.offDiag_card]
    have := hdeg v
    have h3 : (G.outEdges v).card ≤ 3 := by omega
    have hmul : (G.outEdges v).card * (G.outEdges v).card ≤ 3 * (G.outEdges v).card :=
      Nat.mul_le_mul h3 (le_refl _)
    have hsub := Nat.sub_le_sub_right hmul (G.outEdges v).card
    omega
  rw [numPairs]
  omega

end PathGraph

/-! ## The compiled representation of a formula -/

variable {ι F : Type} [Field F] [CharP F 2]

namespace Formula

/-- The affine-product hypercube representation compiled from a formula. -/
noncomputable def rep (f : Formula ι F) (τ : F) : AffineHypercubeRep ι F :=
  PathGraph.graphRep f.toDag.G f.toDag.lab τ

/-- **The compiled representation computes the formula.** -/
theorem rep_value (f : Formula ι F) {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (f.rep τ).value = f.eval := by
  rw [rep, PathGraph.graphRep_value _ _ hτ0 hτ1]
  show f.toDag.value = f.eval
  exact f.toDag_value

/-- **Every affine factor of the compiled representation has support at most three.** -/
theorem rep_supportLE_three (f : Formula ι F) (τ : F) : (f.rep τ).SupportLE 3 :=
  PathGraph.graphRep_supportLE_three _ _ τ (fun v => (f.toDag_goodDeg).2.2.2.2 v)
    (fun a => f.toDag_goodLab a)

/-- The number of ordered pair-exclusion constraints of the formula graph. -/
theorem numPairs_le (f : Formula ι F) :
    f.toDag.G.numPairs ≤ 4 * Fintype.card f.toDag.E :=
  PathGraph.numPairs_le _ fun v => (f.toDag_goodDeg).2.2.2.2 v

/-- **Size accounting, summed Boolean variables:** `q = 3|E| + 2P ≤ 11 |E| = O(size f)`. -/
theorem rep_numAux_le (f : Formula ι F) (τ : F) :
    (f.rep τ).numAux ≤ 11 * (f.leaves + 4 * f.addGates + f.mulGates) := by
  rw [rep, PathGraph.graphRep_numAux]
  have h := f.numPairs_le
  rw [f.toDag_card_E] at h ⊢
  omega

/-- **Size accounting, affine factors:** `M = |V| + 4(|E| + P) ≤ |V| + 20|E| = O(size f)`. -/
theorem rep_numFactors_le (f : Formula ι F) (τ : F) :
    (f.rep τ).numFactors
      ≤ (2 * f.leaves + 2 * f.addGates) + 20 * (f.leaves + 4 * f.addGates + f.mulGates) := by
  rw [rep, PathGraph.graphRep_numFactors]
  have h := f.numPairs_le
  rw [f.toDag_card_E] at h ⊢
  rw [f.toDag_card_V]
  omega

/-- **The main finite compiler theorem.**

Over a field `F` of characteristic two containing an element `τ ∉ {0, 1}`, every binary
division-free arithmetic formula `f` has a finite affine-product Boolean-hypercube
representation

```
f(X) = ∑_{u : aux → Bool} ∏_j A_j(X, u)
```

in which every affine factor `A_j` mentions at most three variables, the number `q` of
summed Boolean auxiliaries is at most `44 · size f` and the number `M` of affine factors is
at most `84 · size f`; in particular both are `O(size f)`. -/
theorem has_supportThree_affineHypercubeRepresentation (f : Formula ι F) {τ : F}
    (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    ∃ R : AffineHypercubeRep ι F,
      R.Represents f.eval ∧ R.SupportLE 3 ∧
        R.numAux ≤ 44 * f.size ∧ R.numFactors ≤ 84 * f.size := by
  refine ⟨f.rep τ, f.rep_value hτ0 hτ1, f.rep_supportLE_three τ, ?_, ?_⟩
  · have h := f.rep_numAux_le τ
    have : f.size = f.leaves + f.addGates + f.mulGates := rfl
    omega
  · have h := f.rep_numFactors_le τ
    have : f.size = f.leaves + f.addGates + f.mulGates := rfl
    omega

end Formula

end VNP1Char2
