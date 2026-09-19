/-
# The class-level support-two bridge

Strictly append-only: the frozen support-three class layer (`PFamily`, `Nondeterminism`,
`ClassLevel`) is used as a black box and is neither modified nor reproved.

Over a field `F` of characteristic two containing an element `τ ∉ {0,1}` we prove

* `nondetVPe_subset_VNP1LE2` : `N(VP_e(F)) ⊆ VNP₁^{[≤2]}(F)`.  The outer witness cube of
  the nondeterministic family and the fresh cube of the support-two compiled
  representation are flattened into a single Boolean cube on the *disjoint union* of their
  index sets; the flattening introduces no new summed variable and changes no factor, so
  support `≤ 2` is preserved.
* `VNP1LE2_subset_nondetVPe` : the reverse containment, through the frozen support-three
  theorem (`SupportLE 2 → SupportLE 3`).
* `nondetVPe_eq_VNP1LE2` : the internal class equality `N(VP_e(F)) = VNP₁^{[≤2]}(F)`.

Finally, because the internal affine-factor convention (`AffineForm`: a constant plus an
explicit list of coefficient/variable pairs) is *narrower* than the literature convention
(an arbitrary polynomial of total degree at most one, i.e. an edge label of a width-one
ABP), we add the minimal literature bridge

* `VNP1LE2_subset_VNP1BIZ` : `VNP₁^{[≤2]}(F) ⊆ VNP₁,BIZ(F)`,

where `VNP1BIZ` asks only for a Boolean-hypercube sum of a product of polynomially many
polynomials of total degree at most one.  No literature theorem (neither Valiant's
`VNP_e = VNP` nor any statement of Bringmann–Ikenmeyer–Zuiddam) is assumed here, as an
axiom or otherwise.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevel
import RequestProject.AlgebraicComplexity.VNP1Char2.MainCompilerTwo

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial AffineForm

variable {F : Type} [Field F]

/-! ## The support-two class -/

/-- **`VNP₁^{[≤2]}`**: families admitting, for every `n`, an affine-product
Boolean-hypercube representation with polynomially bounded cube dimension `q n` and factor
count `M n`, in which every affine factor has support at most **two** (counted over
original *and* hypercube variables). -/
def VNP1LE2 (f : PolyFamily F) : Prop :=
  PolyBounded f.nvars ∧
    ∃ (R : ∀ n, AffineHypercubeRep (Fin (f.nvars n)) F) (q M : ℕ → ℕ),
      PolyBounded q ∧ PolyBounded M ∧
        ∀ n, (R n).Represents (f.poly n) ∧ (R n).SupportLE 2 ∧
          (R n).numAux ≤ q n ∧ (R n).numFactors ≤ M n

theorem VNP1LE2.toVNP1LE3 {f : PolyFamily F} (h : VNP1LE2 f) : VNP1LE3 f := by
  obtain ⟨hv, R, q, M, hq, hM, h⟩ := h
  exact ⟨hv, R, q, M, hq, hM, fun n =>
    ⟨(h n).1, fun A hA => le_trans ((h n).2.1 A hA) (by norm_num), (h n).2.2.1, (h n).2.2.2⟩⟩

/-! ## `N(VP_e) ⊆ VNP₁^{[≤2]}` -/

/-- **The load-bearing support-two class theorem.**  Over a characteristic-two field with
an element `τ ∉ {0,1}`, the nondeterministic closure of the formula class is contained in
the support-two affine-product hypercube class. -/
theorem nondetVPe_subset_VNP1LE2 [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1LE2 f := by
  obtain ⟨hv, g, p, q, ⟨hgv, φ, s, hs, hφ⟩, hp, hq, hrep⟩ := hf
  classical
  refine ⟨hv, fun n =>
      ((φ (q n)).rep2 τ).reindex (Fin (p n) ⊕ ((φ (q n)).rep2 τ).aux)
        (nondetRho (hrep n).1 _),
    (fun n => p n + 26 * s (q n)), (fun n => 70 * s (q n)),
    hp.add (PolyBounded.const_mul 26 (hs.comp hq)), PolyBounded.const_mul 70 (hs.comp hq),
    fun n => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- the representation computes `f n`
    have hval : ((φ (q n)).rep2 τ).value = g.poly (q n) := by
      rw [Formula.rep2_value _ hτ0 hτ1, (hφ (q n)).1]
    show AffineHypercubeRep.value _ = _
    refine Eq.trans ?_ (hrep n).2.symm
    rw [AffineHypercubeRep.reindex_value]
    rw [Finset.sum_congr rfl fun w (_ : w ∈ Finset.univ) =>
      congrArg List.prod (List.map_congr_left fun B _ => by
        rw [elim_comp_nondetRho (hrep n).1])]
    rw [← Equiv.sum_comp
      (Equiv.sumArrowEquivProdArrow (Fin (p n)) ((φ (q n)).rep2 τ).aux Bool).symm,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hval, AffineHypercubeRep.aeval_value]
    rfl
  · -- support at most two
    exact AffineHypercubeRep.reindex_supportLE _ _ _ ((φ (q n)).rep2_supportLE_two τ)
  · -- number of summed Boolean variables
    show Fintype.card (Fin (p n) ⊕ ((φ (q n)).rep2 τ).aux) ≤ p n + 26 * s (q n)
    have h1 : ((φ (q n)).rep2 τ).numAux ≤ 26 * (φ (q n)).size := (φ (q n)).rep2_numAux_le τ
    have h2 : (φ (q n)).size ≤ s (q n) := (hφ (q n)).2
    have hcard : Fintype.card (Fin (p n) ⊕ ((φ (q n)).rep2 τ).aux)
        = p n + ((φ (q n)).rep2 τ).numAux := by
      simp [AffineHypercubeRep.numAux]
    have h3 : 26 * (φ (q n)).size ≤ 26 * s (q n) := Nat.mul_le_mul_left _ h2
    omega
  · -- number of affine factors
    show AffineHypercubeRep.numFactors _ ≤ 70 * s (q n)
    rw [AffineHypercubeRep.reindex_numFactors]
    have h1 : ((φ (q n)).rep2 τ).numFactors ≤ 70 * (φ (q n)).size :=
      (φ (q n)).rep2_numFactors_le τ
    have h2 : (φ (q n)).size ≤ s (q n) := (hφ (q n)).2
    have h3 : 70 * (φ (q n)).size ≤ 70 * s (q n) := Nat.mul_le_mul_left _ h2
    omega

/-- `VP_e(F) ⊆ VNP₁^{[≤2]}(F)`. -/
theorem VPe_subset_VNP1LE2 [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : VPe f) : VNP1LE2 f :=
  nondetVPe_subset_VNP1LE2 hτ0 hτ1 hf.toVNPe

/-- **Reverse containment**, inherited from the frozen support-three layer. -/
theorem VNP1LE2_subset_nondetVPe {f : PolyFamily F} (hf : VNP1LE2 f) :
    NondetClosure VPe f :=
  VNP1LE3_subset_nondetVPe hf.toVNP1LE3

/-- **The internal class equality** `N(VP_e(F)) = VNP₁^{[≤2]}(F)` over a characteristic-two
field with an element `τ ∉ {0,1}`. -/
theorem nondetVPe_eq_VNP1LE2 [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE2 f := by
  funext f
  exact propext ⟨nondetVPe_subset_VNP1LE2 hτ0 hτ1, VNP1LE2_subset_nondetVPe⟩

/-- The class equality under the canonical hypothesis `∃ τ, τ ≠ 0 ∧ τ ≠ 1`, which also
covers infinite characteristic-two fields. -/
theorem nondetVPe_eq_VNP1LE2_of_exists_tau [CharP F 2] (hτ : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE2 f := by
  obtain ⟨τ, hτ0, hτ1⟩ := hτ
  exact nondetVPe_eq_VNP1LE2 hτ0 hτ1

/-- The class equality for every finite field of characteristic two with more than two
elements. -/
theorem nondetVPe_eq_VNP1LE2_of_natCard [Finite F] [CharP F 2] (h : 2 < Nat.card F) :
    (fun f : PolyFamily F => NondetClosure VPe f) = fun f : PolyFamily F => VNP1LE2 f :=
  nondetVPe_eq_VNP1LE2_of_exists_tau (exists_tau_of_two_lt_natCard h)

/-! ## The minimal width-one-ABP literature bridge -/

namespace AffineForm

variable {σ : Type}

/-- The polynomial of an affine form has total degree at most one: it is a legal edge label
of a width-one algebraic branching program. -/
theorem toPoly_totalDegree_le_one (A : AffineForm σ F) : (A.toPoly).totalDegree ≤ 1 := by
  unfold toPoly
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le (by simp) ?_)
  induction A.terms with
  | nil => simp
  | cons q l ih =>
      rw [List.map_cons, List.sum_cons]
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ih)
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      simp

end AffineForm

/-- **`VNP₁,BIZ`** (the literature convention): families that are a Boolean-hypercube sum,
over polynomially many witness bits, of a product of polynomially many polynomials of total
degree at most one — that is, of the edge labels of a width-one algebraic branching
program.  This convention is *weaker* (broader) than the internal `AffineForm` convention,
so the containment below is the honest direction for a literature bridge. -/
def VNP1BIZ (f : PolyFamily F) : Prop :=
  PolyBounded f.nvars ∧
    ∃ (q M : ℕ → ℕ) (L : ∀ n, List (MvPolynomial (Fin (f.nvars n) ⊕ Fin (q n)) F)),
      PolyBounded q ∧ PolyBounded M ∧ ∀ n,
        (∀ P ∈ L n, P.totalDegree ≤ 1) ∧ (L n).length ≤ M n ∧
          f.poly n = ∑ b : Fin (q n) → Bool,
            ((L n).map fun P => aeval (Sum.elim X fun j => boolVal (b j)) P).prod

/-- **The literature bridge.**  Every support-two affine-product hypercube family is a
width-one-ABP hypercube family in the sense of the literature. -/
theorem VNP1LE2_subset_VNP1BIZ {f : PolyFamily F} (hf : VNP1LE2 f) : VNP1BIZ f := by
  obtain ⟨hv, R, q, M, hq, hM, h⟩ := hf
  classical
  let e : ∀ n, (R n).aux ≃ Fin ((R n).numAux) := fun n => Fintype.equivFin (R n).aux
  let ρ : ∀ n, Fin (f.nvars n) ⊕ (R n).aux → Fin (f.nvars n) ⊕ Fin ((R n).numAux) :=
    fun n => Sum.map id (e n)
  refine ⟨hv, (fun n => (R n).numAux), M, (fun n => ((R n).factors.map
      fun A => (mapVar (ρ n) A).toPoly)),
    PolyBounded.mono (fun n => (h n).2.2.1) hq, hM, fun n => ⟨?_, ?_, ?_⟩⟩
  · intro P hP
    obtain ⟨A, -, rfl⟩ := List.mem_map.mp hP
    exact AffineForm.toPoly_totalDegree_le_one _
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

/-- `N(VP_e(F)) ⊆ VNP₁,BIZ(F)`: the compiled families are width-one-ABP hypercube families
in the literature sense. -/
theorem nondetVPe_subset_VNP1BIZ [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1BIZ f :=
  VNP1LE2_subset_VNP1BIZ (nondetVPe_subset_VNP1LE2 hτ0 hτ1 hf)

end VNP1Char2
