/-
# The class-level bridge

This file closes the owner `CLASS_LEVEL_VP_e_TO_VNP1` recorded in `OpenOwners.lean`,
strictly by appending to the existing layer: the finite compiler
`Formula.has_supportThree_affineHypercubeRepresentation` (and the underlying
`Formula.rep`) is used as a black box and is neither modified nor reproved.

Over a field `F` of characteristic two containing an element `τ ∉ {0,1}` we prove

* `nondetVPe_subset_VNP1LE3` : `N(VP_e(F)) ⊆ VNP₁^{[≤3]}(F)` — the load-bearing theorem.
  The outer witness cube `b` of the nondeterministic family and the fresh cube `u` of the
  compiled representation are flattened into a single Boolean cube on the *disjoint union*
  of their index sets.  The outer witness bits stay genuine variables of the compiled
  formula (they are the last `p n` variables of `g_{q(n)}`), and the compiler's auxiliaries
  are disjoint from them by construction; the flattening itself introduces no summed
  Boolean variable of its own.
* `VPe_subset_VNP1LE3` : `VP_e(F) ⊆ VNP₁^{[≤3]}(F)`, the special case of an empty outer
  cube.
* `VNP1LE3_subset_nondetVPe` : `VNP₁^{[≤3]}(F) ⊆ N(VP_e(F))`, because a product of
  polynomially many affine forms of support at most three is an arithmetic formula of
  polynomially bounded size, the hypercube variables being appended to the variable list.
* `nondetVPe_eq_VNP1LE3` : the resulting internal equality
  `N(VP_e(F)) = VNP₁^{[≤3]}(F)`.

No literature theorem is used: in particular neither Valiant's `VNP_e = VNP` nor any
statement of Bringmann–Ikenmeyer–Zuiddam is assumed here, as an axiom or otherwise, and
nothing in this file identifies `VNP₁^{[≤3]}` with the literature class `VNP`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.Nondeterminism
import RequestProject.AlgebraicComplexity.VNP1Char2.FieldCorollary

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial AffineForm

variable {F : Type} [Field F]

/-! ## Two consequences of the banked size accounting -/

namespace Formula

variable [CharP F 2] {ι : Type}

theorem rep_numAux_le_size (f : Formula ι F) (τ : F) : (f.rep τ).numAux ≤ 44 * f.size := by
  have h := f.rep_numAux_le τ
  have hs : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

theorem rep_numFactors_le_size (f : Formula ι F) (τ : F) :
    (f.rep τ).numFactors ≤ 84 * f.size := by
  have h := f.rep_numFactors_le τ
  have hs : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

end Formula

/-! ## Substituting into a representation -/

namespace AffineHypercubeRep

variable {ι : Type} {M : Type} [CommRing M] [Algebra F M]

/-- Substituting polynomials for the original variables of a representation preserves the
hypercube shape: the factors are simply evaluated at the substituted assignment. -/
theorem aeval_value (R : AffineHypercubeRep ι F) (σ : ι → M) :
    aeval σ R.value =
      ∑ u : R.aux → Bool,
        (R.factors.map fun B => B.eval (Sum.elim σ fun a => boolVal (u a))).prod := by
  unfold value
  rw [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def]
  refine congrArg List.prod (List.map_congr_left fun B _ => ?_)
  rw [AffineForm.map_eval (aeval σ) B (R.subst u)]
  congr 1
  funext x
  rcases x with i | a
  · simp [subst]
  · cases hu : u a <;> simp [subst, hu]

end AffineHypercubeRep

/-! ## `N(VP_e) ⊆ VNP₁^{[≤3]}` -/

/-- The variable renaming that merges the outer witness bits and the compiler's fresh
auxiliaries into one Boolean cube indexed by their disjoint union. -/
def nondetRho {m k N : ℕ} (h : N ≤ m + k) (A : Type) :
    Fin N ⊕ A → Fin m ⊕ (Fin k ⊕ A) :=
  Sum.elim (fun i => Sum.elim Sum.inl (fun j => Sum.inr (Sum.inl j)) (witnessIdx h i))
    fun a => Sum.inr (Sum.inr a)

theorem elim_comp_nondetRho {m k N : ℕ} (h : N ≤ m + k) (A : Type)
    (w : (Fin k ⊕ A) → Bool) :
    (Sum.elim (fun i => (X i : MvPolynomial (Fin m) F)) fun c => boolVal (w c)) ∘
        nondetRho h A
      = Sum.elim (witnessSubst m k fun j => w (Sum.inl j)) fun a => boolVal (w (Sum.inr a)) := by
  funext x
  rcases x with i | a
  · show Sum.elim _ _ (Sum.elim Sum.inl (fun j => Sum.inr (Sum.inl j)) (witnessIdx h i)) = _
    rw [witnessSubst_eq_elim h]
    rcases hw : witnessIdx h i with j | j <;> simp [hw]
  · rfl

/-- **The load-bearing class theorem.**  Over a characteristic-two field with an element
`τ ∉ {0,1}`, the nondeterministic closure of the formula class is contained in the
support-three affine-product hypercube class. -/
theorem nondetVPe_subset_VNP1LE3 [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1LE3 f := by
  obtain ⟨hv, g, p, q, ⟨hgv, φ, s, hs, hφ⟩, hp, hq, hrep⟩ := hf
  classical
  refine ⟨hv, fun n =>
      ((φ (q n)).rep τ).reindex (Fin (p n) ⊕ ((φ (q n)).rep τ).aux)
        (nondetRho (hrep n).1 _),
    (fun n => p n + 44 * s (q n)), (fun n => 84 * s (q n)),
    hp.add (PolyBounded.const_mul 44 (hs.comp hq)), PolyBounded.const_mul 84 (hs.comp hq),
    fun n => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- the representation computes `f n`
    have hval : ((φ (q n)).rep τ).value = g.poly (q n) := by
      rw [Formula.rep_value _ hτ0 hτ1, (hφ (q n)).1]
    show AffineHypercubeRep.value _ = _
    refine Eq.trans ?_ (hrep n).2.symm
    rw [AffineHypercubeRep.reindex_value]
    rw [Finset.sum_congr rfl fun w (_ : w ∈ Finset.univ) =>
      congrArg List.prod (List.map_congr_left fun B _ => by
        rw [elim_comp_nondetRho (hrep n).1])]
    rw [← Equiv.sum_comp
      (Equiv.sumArrowEquivProdArrow (Fin (p n)) ((φ (q n)).rep τ).aux Bool).symm,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hval, AffineHypercubeRep.aeval_value]
    rfl
  · -- support at most three
    exact AffineHypercubeRep.reindex_supportLE _ _ _ ((φ (q n)).rep_supportLE_three τ)
  · -- number of summed Boolean variables
    show Fintype.card (Fin (p n) ⊕ ((φ (q n)).rep τ).aux) ≤ p n + 44 * s (q n)
    have h1 : ((φ (q n)).rep τ).numAux ≤ 44 * (φ (q n)).size :=
      (φ (q n)).rep_numAux_le_size τ
    have h2 : (φ (q n)).size ≤ s (q n) := (hφ (q n)).2
    have : Fintype.card (Fin (p n) ⊕ ((φ (q n)).rep τ).aux)
        = p n + ((φ (q n)).rep τ).numAux := by
      simp [AffineHypercubeRep.numAux]
    omega
  · -- number of affine factors
    show AffineHypercubeRep.numFactors _ ≤ 84 * s (q n)
    rw [AffineHypercubeRep.reindex_numFactors]
    have h1 : ((φ (q n)).rep τ).numFactors ≤ 84 * (φ (q n)).size :=
      (φ (q n)).rep_numFactors_le_size τ
    have h2 : (φ (q n)).size ≤ s (q n) := (hφ (q n)).2
    omega

/-- `VP_e(F) ⊆ VNP₁^{[≤3]}(F)`. -/
theorem VPe_subset_VNP1LE3 [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : VPe f) : VNP1LE3 f :=
  nondetVPe_subset_VNP1LE3 hτ0 hτ1 hf.toVNPe

/-! ## `VNP₁^{[≤3]} ⊆ N(VP_e)` -/

/-- The renaming that turns the auxiliaries of a representation into the last `k`
variables of a polynomial in `m + k` variables. -/
def repRho (m k : ℕ) {A : Type} (e : A ≃ Fin k) : Fin m ⊕ A → Fin (m + k) :=
  Sum.elim (Fin.castAdd k) fun a => Fin.natAdd m (e a)

theorem witnessSubst_comp_repRho (m k : ℕ) {A : Type} (e : A ≃ Fin k) (b : Fin k → Bool) :
    (witnessSubst (F := F) m k (N := m + k) b) ∘ repRho m k e
      = Sum.elim (fun i => (X i : MvPolynomial (Fin m) F)) fun a => boolVal (b (e a)) := by
  funext x
  rcases x with i | a
  · show witnessSubst m k b (Fin.castAdd k i) = X i
    simp [witnessSubst, i.2]
  · show witnessSubst m k b (Fin.natAdd m (e a)) = boolVal (b (e a))
    have h2 : ¬ (m + ((e a : Fin k) : ℕ) < m) := by omega
    have h3 : m + ((e a : Fin k) : ℕ) - m = ((e a : Fin k) : ℕ) := by omega
    simp [witnessSubst, h2, h3, (e a).2]

/-- **Reverse containment.**  A product of polynomially many affine forms of support at
most three is an arithmetic formula of polynomially bounded size, so every support-three
affine-product hypercube family lies in the nondeterministic closure of the formula
class. -/
theorem VNP1LE3_subset_nondetVPe {f : PolyFamily F} (hf : VNP1LE3 f) :
    NondetClosure VPe f := by
  obtain ⟨hv, R, q, M, hq, hM, h⟩ := hf
  classical
  -- an enumeration of the auxiliaries of the `n`-th representation
  let e : ∀ n, (R n).aux ≃ Fin ((R n).numAux) := fun n => Fintype.equivFin (R n).aux
  -- the list of affine factors, read in the merged variable set
  let L : ∀ n, List (AffineForm (Fin (f.nvars n + (R n).numAux)) F) := fun n =>
    (R n).factors.map (mapVar (repRho (f.nvars n) ((R n).numAux) (e n)))
  have hnvars : PolyBounded fun n => f.nvars n + (R n).numAux :=
    hv.add (PolyBounded.mono (fun n => (h n).2.2.1) hq)
  refine ⟨hv, ⟨fun n => f.nvars n + (R n).numAux, fun n => ((L n).map AffineForm.toPoly).prod⟩,
    (fun n => (R n).numAux), (fun n => n), ⟨hnvars, fun n => Formula.prodList
      ((L n).map AffineForm.toFormula), (fun n => 14 * M n + 1),
      (PolyBounded.const_mul 14 hM).add (polyBounded_const 1), fun n => ⟨?_, ?_⟩⟩,
    PolyBounded.mono (fun n => (h n).2.2.1) hq, polyBounded_id, fun n => ⟨le_rfl, ?_⟩⟩
  · -- the formula computes the product of the affine factors
    show (Formula.prodList _).eval = _
    rw [Formula.prodList_eval]
    simp only [List.map_map, Function.comp_def, AffineForm.toFormula_eval]
  · -- polynomially bounded formula size
    show (Formula.prodList _).size ≤ 14 * M n + 1
    have hlen : ((L n).map AffineForm.toFormula).length ≤ M n := by
      have := (h n).2.2.2
      simpa [L, AffineHypercubeRep.numFactors] using this
    have hc : ∀ ψ ∈ (L n).map AffineForm.toFormula, ψ.size ≤ 13 := by
      intro ψ hψ
      simp only [List.mem_map] at hψ
      obtain ⟨B, hB, rfl⟩ := hψ
      rw [AffineForm.toFormula_size]
      simp only [L, List.mem_map] at hB
      obtain ⟨C, hC, rfl⟩ := hB
      have := (h n).2.1 C hC
      rw [AffineForm.numVars_mapVar]
      omega
    have := Formula.prodList_size_le ((L n).map AffineForm.toFormula) 13 hc
    have h14 : (13 + 1) * ((L n).map AffineForm.toFormula).length ≤ 14 * M n :=
      Nat.mul_le_mul_left _ hlen
    omega
  · -- the hypercube sum of the compiled formula reproduces `f n`
    have hR : (R n).value = f.poly n := (h n).1
    rw [← hR]
    show _ = ∑ b : Fin ((R n).numAux) → Bool, aeval _ (((L n).map AffineForm.toPoly).prod)
    have step : ∀ b : Fin ((R n).numAux) → Bool,
        aeval (witnessSubst (f.nvars n) ((R n).numAux) b)
            (((L n).map AffineForm.toPoly).prod)
          = ((R n).factors.map fun B =>
              B.eval ((R n).subst fun a => b (e n a))).prod := by
      intro b
      rw [map_list_prod]
      simp only [L, List.map_map, Function.comp_def]
      refine congrArg List.prod (List.map_congr_left fun B _ => ?_)
      rw [AffineForm.aeval_toPoly, AffineForm.eval_mapVar,
        witnessSubst_comp_repRho (f.nvars n) ((R n).numAux) (e n) b]
      rfl
    rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => step b,
      show (R n).value = ∑ u : (R n).aux → Bool,
        ((R n).factors.map fun B => B.eval ((R n).subst u)).prod from rfl]
    exact (Fintype.sum_equiv (Equiv.arrowCongr (e n).symm (Equiv.refl Bool)) _ _
      fun b => rfl).symm

/-- **The internal class equality** `N(VP_e(F)) = VNP₁^{[≤3]}(F)` over a characteristic-two
field with an element `τ ∉ {0,1}`. -/
theorem nondetVPe_eq_VNP1LE3 [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE3 f := by
  funext f
  exact propext ⟨nondetVPe_subset_VNP1LE3 hτ0 hτ1, VNP1LE3_subset_nondetVPe⟩

/-- `N(VP_e(F)) ⊆ VNP₁(F)` (no support restriction). -/
theorem nondetVPe_subset_VNP1 [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1 f :=
  (nondetVPe_subset_VNP1LE3 hτ0 hτ1 hf).toVNP1

/-! ## Field corollaries

The canonical hypothesis is `char F = 2` together with `∃ τ : F, τ ≠ 0 ∧ τ ≠ 1`, which also
covers infinite fields.  For finite fields it follows from `2 < Nat.card F`. -/

/-- The class equality under the canonical hypothesis `∃ τ, τ ≠ 0 ∧ τ ≠ 1`. -/
theorem nondetVPe_eq_VNP1LE3_of_exists_tau [CharP F 2] (hτ : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE3 f := by
  obtain ⟨τ, hτ0, hτ1⟩ := hτ
  exact nondetVPe_eq_VNP1LE3 hτ0 hτ1

/-- The class equality for every finite field of characteristic two with more than two
elements. -/
theorem nondetVPe_eq_VNP1LE3_of_natCard [Finite F] [CharP F 2] (h : 2 < Nat.card F) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE3 f :=
  nondetVPe_eq_VNP1LE3_of_exists_tau (exists_tau_of_two_lt_natCard h)

/-- A characteristic-two field with exactly two elements is `F₂`.  This is recorded for
completeness only; it is *not* used by any theorem above. -/
theorem ringEquiv_zmod_two_of_card_eq_two [Fintype F] [CharP F 2] (h : Fintype.card F = 2) :
    Nonempty (ZMod 2 ≃+* F) :=
  ⟨ZMod.ringEquiv F h⟩

end VNP1Char2
