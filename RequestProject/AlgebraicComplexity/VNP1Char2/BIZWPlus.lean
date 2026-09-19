/-
# The literal `w+` support-two bridge

Strictly append-only.  Nothing in the existing project is modified, renamed, weakened or
reproved; both banked compilers are untouched.

The internal literature-shaped class `VNP1BIZ` (in `ClassLevelTwo`) asks only that every
factor polynomial has **total degree at most one**.  That is an unrestricted affine
width-one representation, and it does *not* by itself encode the stronger `w+` requirement
of the width-one literature that every affine edge label involve at most **two** variables.

This file adds the literal support-two literature-shaped class

* `VNP1BIZWPlus` — each factor polynomial satisfies *both* `totalDegree ≤ 1` *and*
  `vars.card ≤ 2`,

and proves

* `VNP1LE2_subset_VNP1BIZWPlus` : `VNP₁^{[≤2]}(F) ⊆ VNP₁,BIZ-w+(F)`, consuming the already
  certified syntactic `SupportLE 2` property of the compiled representations and bridging
  syntactic affine-form support (`AffineForm.numVars`, the length of the coefficient list)
  to the semantic variable-set cardinality (`MvPolynomial.vars.card`) used in the
  literature-shaped class;
* `VNP1BIZWPlus.toVNP1BIZ` : the forgetful inclusion `VNP₁,BIZ-w+(F) ⊆ VNP₁,BIZ(F)`;
* `nondetVPe_subset_VNP1BIZWPlus` : the resulting containment for the compiled families.

No external literature theorem (neither Valiant's `VNP_e = VNP` nor any statement of
Bringmann–Ikenmeyer–Zuiddam) is assumed here, as an axiom or otherwise.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.PFamilyDegree

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial AffineForm

variable {F : Type} [Field F]

/-! ## Syntactic support bounds the semantic variable set -/

namespace AffineForm

variable {σ : Type} [DecidableEq σ]

theorem vars_termSum_subset (l : List (F × σ)) :
    ((l.map fun p => (C p.1 * X p.2 : MvPolynomial σ F)).sum).vars
      ⊆ (l.map Prod.snd).toFinset := by
  induction l with
  | nil => simp
  | cons p l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.toFinset_cons]
      refine subset_trans (MvPolynomial.vars_add_subset _ _) ?_
      refine Finset.union_subset ?_ (subset_trans ih (Finset.subset_insert _ _))
      refine subset_trans (MvPolynomial.vars_mul _ _) ?_
      refine Finset.union_subset ?_ ?_
      · simp
      · intro i hi
        rw [MvPolynomial.vars_X, Finset.mem_singleton] at hi
        subst hi
        exact Finset.mem_insert_self _ _

/-- The variables actually occurring in the polynomial of an affine form are among the
variables listed in its linear terms. -/
theorem toPoly_vars_subset (A : AffineForm σ F) : A.toPoly.vars ⊆ A.vars := by
  unfold toPoly vars
  refine subset_trans (MvPolynomial.vars_add_subset _ _) (Finset.union_subset ?_ ?_)
  · simp
  · exact vars_termSum_subset A.terms

/-- **The syntactic-to-semantic support bridge**: an affine form with at most `n` linear
terms yields a polynomial mentioning at most `n` variables. -/
theorem toPoly_vars_card_le (A : AffineForm σ F) : A.toPoly.vars.card ≤ A.numVars :=
  le_trans (Finset.card_le_card (toPoly_vars_subset A)) A.card_vars_le

end AffineForm

/-! ## The literal `w+` support-two class -/

/-- **`VNP₁,BIZ-w+`** (the literal width-one `w+` literature convention): families that are
a Boolean-hypercube sum, over polynomially many witness bits, of a product of polynomially
many polynomials which are *both* of total degree at most one *and* mention at most two
variables.  The second condition is exactly the `w+` support restriction on the affine edge
labels of a width-one algebraic branching program. -/
def VNP1BIZWPlus (f : PolyFamily F) : Prop :=
  PolyBounded f.nvars ∧
    ∃ (q M : ℕ → ℕ) (L : ∀ n, List (MvPolynomial (Fin (f.nvars n) ⊕ Fin (q n)) F)),
      PolyBounded q ∧ PolyBounded M ∧ ∀ n,
        (∀ P ∈ L n, P.totalDegree ≤ 1 ∧ P.vars.card ≤ 2) ∧ (L n).length ≤ M n ∧
          f.poly n = ∑ b : Fin (q n) → Bool,
            ((L n).map fun P => aeval (Sum.elim X fun j => boolVal (b j)) P).prod

/-- **The forgetful inclusion** `VNP₁,BIZ-w+(F) ⊆ VNP₁,BIZ(F)`. -/
theorem VNP1BIZWPlus.toVNP1BIZ {f : PolyFamily F} (hf : VNP1BIZWPlus f) : VNP1BIZ f := by
  obtain ⟨hv, q, M, L, hq, hM, h⟩ := hf
  exact ⟨hv, q, M, L, hq, hM, fun n =>
    ⟨fun P hP => ((h n).1 P hP).1, (h n).2.1, (h n).2.2⟩⟩

/-- **The literal `w+` bridge**: `VNP₁^{[≤2]}(F) ⊆ VNP₁,BIZ-w+(F)`.

The proof consumes the certified syntactic property `SupportLE 2` of the compiled
representations (every affine factor has at most two linear terms) and converts it into the
semantic condition used by the literature-shaped class (the factor polynomial mentions at
most two variables), alongside the total-degree-at-most-one condition. -/
theorem VNP1LE2_subset_VNP1BIZWPlus {f : PolyFamily F} (hf : VNP1LE2 f) : VNP1BIZWPlus f := by
  obtain ⟨hv, R, q, M, hq, hM, h⟩ := hf
  classical
  let e : ∀ n, (R n).aux ≃ Fin ((R n).numAux) := fun n => Fintype.equivFin (R n).aux
  let ρ : ∀ n, Fin (f.nvars n) ⊕ (R n).aux → Fin (f.nvars n) ⊕ Fin ((R n).numAux) :=
    fun n => Sum.map id (e n)
  refine ⟨hv, (fun n => (R n).numAux), M, (fun n => ((R n).factors.map
      fun A => (mapVar (ρ n) A).toPoly)),
    PolyBounded.mono (fun n => (h n).2.2.1) hq, hM, fun n => ⟨?_, ?_, ?_⟩⟩
  · intro P hP
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hP
    refine ⟨AffineForm.toPoly_totalDegree_le_one _, ?_⟩
    refine le_trans (AffineForm.toPoly_vars_card_le _) ?_
    rw [AffineForm.numVars_mapVar]
    exact (h n).2.1 A hA
  · simpa [AffineHypercubeRep.numFactors] using (h n).2.2.2
  · -- the hypercube sum of the width-one product reproduces `f n`
    have hR : (R n).value = f.poly n := (h n).1
    rw [← hR]
    have step : ∀ b : Fin ((R n).numAux) → Bool,
        (((R n).factors.map fun A => (mapVar (ρ n) A).toPoly).map fun P =>
            aeval (Sum.elim X fun j => boolVal (b j)) P).prod
          = ((R n).factors.map fun A => A.eval ((R n).subst fun a => b (e n a))).prod := by
      intro b
      simp only [List.map_map, Function.comp_def]
      refine congrArg List.prod (List.map_congr_left fun A _ => ?_)
      rw [AffineForm.aeval_toPoly, AffineForm.eval_mapVar]
      congr 1
      funext c
      rcases c with i | a
      · rfl
      · rfl
    rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => step b,
      show (R n).value = ∑ u : (R n).aux → Bool,
        ((R n).factors.map fun A => A.eval ((R n).subst u)).prod from rfl]
    exact (Fintype.sum_equiv (Equiv.arrowCongr (e n).symm (Equiv.refl Bool)) _ _
      fun b => rfl).symm

/-- The compiled families of the main theorem are literal `w+` width-one hypercube
families. -/
theorem nondetVPe_subset_VNP1BIZWPlus [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1BIZWPlus f :=
  VNP1LE2_subset_VNP1BIZWPlus (nondetVPe_subset_VNP1LE2 hτ0 hτ1 hf)

/-- `VP_e(F) ⊆ VNP₁,BIZ-w+(F)`. -/
theorem VPe_subset_VNP1BIZWPlus [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : VPe f) : VNP1BIZWPlus f :=
  VNP1LE2_subset_VNP1BIZWPlus (VPe_subset_VNP1LE2 hτ0 hτ1 hf)

/-- The `w+` bridge in standard-p-family form: the target family is a standard p-family as
well. -/
theorem nondetVPe_subset_VNP1BIZWPlus_standard [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1BIZWPlus f ∧ IsPFamily f :=
  ⟨nondetVPe_subset_VNP1BIZWPlus hτ0 hτ1 hf, nondetVPe_isPFamily hf⟩

end VNP1Char2
