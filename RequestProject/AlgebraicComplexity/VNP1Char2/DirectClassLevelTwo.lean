/-
# The direct class-level forward containment

An independent proof of the load-bearing forward containment

```
N(VP_e(F)) ⊆ VNP₁^{[≤2]}(F)
```

over a field of characteristic two containing an element `τ ∉ {0,1}`, obtained from the
**direct formula-tree activation compiler** (`DirectFormulaCompiler.lean`) instead of the
frozen graph/path compiler.  The class definitions (`PolyBounded`, `PolyFamily`, `VPe`,
`NondetClosure`, `VNP1LE2`) are reused verbatim; the only compiler input is

* `Formula.directRep_value`, `directRep_supportLE_two`, `directRep_numAux_le`,
  `directRep_numFactors_le`.

None of `Formula.rep2_value`, `Formula.has_supportTwo_affineHypercubeRepresentation`,
`PathGraph.graphRep2_value` or any other graph/path correctness theorem is used in the
proof of `nondetVPe_subset_VNP1LE2_direct`.

As in the frozen proof, the outer witness cube of the nondeterministic family and the
compiler's fresh cube are merged over the *disjoint union* of their index sets, so no
auxiliary of the compiler is identified with a witness bit, no summed variable is added,
and no factor is changed — hence support `≤ 2` is preserved.

Afterwards (and only afterwards) the already-proved reverse containment and the
literature-shaped width-one bridge are reused to package the results.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevelTwo
import RequestProject.AlgebraicComplexity.VNP1Char2.DirectFormulaCompiler

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial AffineForm

variable {F : Type} [Field F]

/-- **The direct load-bearing class theorem.**  `N(VP_e(F)) ⊆ VNP₁^{[≤2]}(F)`, proved from
the direct formula-tree compiler. -/
theorem nondetVPe_subset_VNP1LE2_direct [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1LE2 f := by
  obtain ⟨hv, g, p, q, ⟨hgv, φ, s, hs, hφ⟩, hp, hq, hrep⟩ := hf
  classical
  refine ⟨hv, fun n =>
      (Formula.directRep τ (φ (q n))).reindex
        (Fin (p n) ⊕ (Formula.directRep τ (φ (q n))).aux) (nondetRho (hrep n).1 _),
    (fun n => p n + 2 * s (q n)), (fun n => 5 * s (q n)),
    hp.add (PolyBounded.const_mul 2 (hs.comp hq)), PolyBounded.const_mul 5 (hs.comp hq),
    fun n => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- the representation computes `f n`
    have hval : (Formula.directRep τ (φ (q n))).value = g.poly (q n) := by
      rw [Formula.directRep_value _ hτ0 hτ1, (hφ (q n)).1]
    show AffineHypercubeRep.value _ = _
    refine Eq.trans ?_ (hrep n).2.symm
    rw [AffineHypercubeRep.reindex_value]
    rw [Finset.sum_congr rfl fun w (_ : w ∈ Finset.univ) =>
      congrArg List.prod (List.map_congr_left fun B _ => by
        rw [elim_comp_nondetRho (hrep n).1])]
    rw [← Equiv.sum_comp
      (Equiv.sumArrowEquivProdArrow (Fin (p n))
        (Formula.directRep τ (φ (q n))).aux Bool).symm,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hval, AffineHypercubeRep.aeval_value]
    rfl
  · -- support at most two
    exact AffineHypercubeRep.reindex_supportLE _ _ _
      (Formula.directRep_supportLE_two τ (φ (q n)))
  · -- number of summed Boolean variables
    show Fintype.card (Fin (p n) ⊕ (Formula.directRep τ (φ (q n))).aux) ≤ p n + 2 * s (q n)
    have h1 : (Formula.directRep τ (φ (q n))).numAux ≤ 2 * (φ (q n)).size :=
      Formula.directRep_numAux_le τ (φ (q n))
    have h2 : (φ (q n)).size ≤ s (q n) := (hφ (q n)).2
    have h3 : 2 * (φ (q n)).size ≤ 2 * s (q n) := Nat.mul_le_mul_left _ h2
    have hcard : Fintype.card (Fin (p n) ⊕ (Formula.directRep τ (φ (q n))).aux)
        = p n + (Formula.directRep τ (φ (q n))).numAux := by
      simp [AffineHypercubeRep.numAux]
    omega
  · -- number of affine factors
    show AffineHypercubeRep.numFactors _ ≤ 5 * s (q n)
    rw [AffineHypercubeRep.reindex_numFactors]
    have h1 : (Formula.directRep τ (φ (q n))).numFactors ≤ 5 * (φ (q n)).size :=
      Formula.directRep_numFactors_le τ (φ (q n))
    have h2 : (φ (q n)).size ≤ s (q n) := (hφ (q n)).2
    have h3 : 5 * (φ (q n)).size ≤ 5 * s (q n) := Nat.mul_le_mul_left _ h2
    omega

/-- `VP_e(F) ⊆ VNP₁^{[≤2]}(F)`, from the direct compiler. -/
theorem VPe_subset_VNP1LE2_direct [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : VPe f) : VNP1LE2 f :=
  nondetVPe_subset_VNP1LE2_direct hτ0 hτ1 hf.toVNPe

/-- **The internal class equality from the direct compiler.**  The forward containment is
the direct one proved above; the reverse containment is the already-banked
`VNP1LE2_subset_nondetVPe`. -/
theorem nondetVPe_eq_VNP1LE2_direct [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE2 f := by
  funext f
  exact propext ⟨nondetVPe_subset_VNP1LE2_direct hτ0 hτ1, VNP1LE2_subset_nondetVPe⟩

/-- The direct class equality under the canonical hypothesis `∃ τ, τ ≠ 0 ∧ τ ≠ 1`. -/
theorem nondetVPe_eq_VNP1LE2_direct_of_exists_tau [CharP F 2] (hτ : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE2 f := by
  obtain ⟨τ, hτ0, hτ1⟩ := hτ
  exact nondetVPe_eq_VNP1LE2_direct hτ0 hτ1

/-- The direct class equality for every finite characteristic-two field with more than two
elements. -/
theorem nondetVPe_eq_VNP1LE2_direct_of_natCard [Finite F] [CharP F 2] (h : 2 < Nat.card F) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE2 f :=
  nondetVPe_eq_VNP1LE2_direct_of_exists_tau (exists_tau_of_two_lt_natCard h)

/-- **Direct corollary through the banked literature-shaped bridge.**  The families of
`N(VP_e(F))` are width-one-ABP Boolean-hypercube families; the forward step is the new
direct containment, the bridge `VNP1LE2_subset_VNP1BIZ` is reused from the frozen layer. -/
theorem nondetVPe_subset_VNP1BIZ_direct [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1BIZ f :=
  VNP1LE2_subset_VNP1BIZ (nondetVPe_subset_VNP1LE2_direct hτ0 hτ1 hf)

end VNP1Char2
