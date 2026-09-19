/-
# The main finite **support-two** compiler theorem

Over a field of characteristic two containing an element `τ ∉ {0, 1}`, every binary
division-free arithmetic formula `f` is compiled into a finite affine-product
Boolean-hypercube representation

```
f(X) = ∑_{u ∈ {0,1}^q} ∏_{j=1}^{M} A_j(X, u)
```

with `q ≤ 26 · size f`, `M ≤ 70 · size f` and every affine factor `A_j` of variable support
at most **two**.

The chain of results used is:

* `Formula.toDag_value` : the formula-generated DAG computes `f`;
* `PathGraph.graphRep2_value` : the support-two compiled representation computes the graph
  polynomial (this is where the ternary cubic error is killed pointwise);
* `PathGraph.graphRep2_supportLE_two` : with the degree invariant of the formula graph and
  one-variable labels, all the affine factors have support at most two;
* `PathGraph.graphRep2_numAux` / `graphRep2_numFactors` : the size accounting, combined
  with `numPairs_le`, `Finset.card_le_univ` and the exact vertex/edge counts.

The memo's coarse constants were `q ≤ 26 s` and `M ≤ 68 s`.  The value `26` is reproduced
exactly; the honest bound obtained here for the factor count is `70 s`, coming from
`M = |V| + 4D + 3(|E| + P) ≤ 2s + 8s + 12s + 48s`, where `D ≤ |V| ≤ 2s` is the number of
degree-three internal vertices and `P ≤ 4|E| ≤ 16s`.  Only `M = O(s)` is used downstream.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.GraphCompilerTwo
import RequestProject.AlgebraicComplexity.VNP1Char2.MainCompiler

namespace VNP1Char2

open scoped BigOperators
open AffineForm MvPolynomial

variable {ι F : Type} [Field F] [CharP F 2]

namespace Formula

/-- The support-two affine-product hypercube representation compiled from a formula. -/
noncomputable def rep2 (f : Formula ι F) (τ : F) : AffineHypercubeRep ι F :=
  PathGraph.graphRep2 f.toDag.G f.toDag.lab τ

/-- **The compiled support-two representation computes the formula.** -/
theorem rep2_value (f : Formula ι F) {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (f.rep2 τ).value = f.eval := by
  rw [rep2, PathGraph.graphRep2_value _ _ hτ0 hτ1]
  show f.toDag.value = f.eval
  exact f.toDag_value

/-- **Every affine factor of the compiled representation has support at most two.** -/
theorem rep2_supportLE_two (f : Formula ι F) (τ : F) : (f.rep2 τ).SupportLE 2 :=
  PathGraph.graphRep2_supportLE_two _ _ τ (fun v => f.toDag_goodDeg.2.2.2.2 v)
    f.toDag_goodDeg.2.2.1 f.toDag_goodDeg.2.2.2.1 (fun a => f.toDag_goodLab a)

/-- **Size accounting, summed Boolean variables:** `q = 2|E| + D + P ≤ 26 · size f`. -/
theorem rep2_numAux_le (f : Formula ι F) (τ : F) : (f.rep2 τ).numAux ≤ 26 * f.size := by
  rw [rep2, PathGraph.graphRep2_numAux]
  have hP := f.numPairs_le
  have hD : (f.toDag.G.ternVerts).card ≤ Fintype.card f.toDag.V :=
    le_trans (Finset.card_le_univ _) (le_of_eq (Finset.card_univ))
  rw [f.toDag_card_E] at hP ⊢
  rw [f.toDag_card_V] at hD
  have hs : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

/-- **Size accounting, affine factors:** `M = |V| + 4D + 3(|E| + P) ≤ 70 · size f`. -/
theorem rep2_numFactors_le (f : Formula ι F) (τ : F) :
    (f.rep2 τ).numFactors ≤ 70 * f.size := by
  rw [rep2, PathGraph.graphRep2_numFactors]
  have hP := f.numPairs_le
  have hD : (f.toDag.G.ternVerts).card ≤ Fintype.card f.toDag.V :=
    le_trans (Finset.card_le_univ _) (le_of_eq (Finset.card_univ))
  rw [f.toDag_card_E] at hP ⊢
  rw [f.toDag_card_V] at hD ⊢
  have hs : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

/-- **The main finite support-two compiler theorem.**

Over a field `F` of characteristic two containing an element `τ ∉ {0, 1}`, every binary
division-free arithmetic formula `f` has a finite affine-product Boolean-hypercube
representation

```
f(X) = ∑_{u : aux → Bool} ∏_j A_j(X, u)
```

in which every affine factor `A_j` mentions at most **two** variables, the number `q` of
summed Boolean auxiliaries is at most `26 · size f` and the number `M` of affine factors is
at most `70 · size f`; in particular both are `O(size f)`. -/
theorem has_supportTwo_affineHypercubeRepresentation (f : Formula ι F) {τ : F}
    (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    ∃ R : AffineHypercubeRep ι F,
      R.Represents f.eval ∧ R.SupportLE 2 ∧
        R.numAux ≤ 26 * f.size ∧ R.numFactors ≤ 70 * f.size :=
  ⟨f.rep2 τ, f.rep2_value hτ0 hτ1, f.rep2_supportLE_two τ, f.rep2_numAux_le τ,
    f.rep2_numFactors_le τ⟩

/-- The support-two representation under the canonical field hypothesis
`∃ τ : F, τ ≠ 0 ∧ τ ≠ 1` (which also covers infinite characteristic-two fields). -/
theorem has_supportTwo_representation_of_exists_tau (f : Formula ι F)
    (hτ : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1) :
    ∃ R : AffineHypercubeRep ι F,
      R.Represents f.eval ∧ R.SupportLE 2 ∧
        R.numAux ≤ 26 * f.size ∧ R.numFactors ≤ 70 * f.size := by
  obtain ⟨τ, hτ0, hτ1⟩ := hτ
  exact f.has_supportTwo_affineHypercubeRepresentation hτ0 hτ1

end Formula

end VNP1Char2
