/-
# The standard p-family total-degree condition

This is a strictly append-only certification layer.  Nothing in the existing project is
modified, renamed, weakened or reproved; in particular both banked compilers (the
graph/path compiler and the direct formula-tree compiler) are untouched.

The internal class infrastructure (`PolyFamily`, `VPe`, `VNP1LE3`, `VNP1LE2`, `VNP1`,
`NondetClosure`) records that a family has *polynomially many variables*, but it does not
literally record the second half of the standard literature definition of a *p-family*,
namely that the **total degree** is polynomially bounded as well.  The internal classes are
therefore (a priori) broader than the standard literature universe.

This file closes that gap:

* `PolyDegreeBounded f` — the total degree of the `n`-th member is polynomially bounded;
* `IsPFamily f` — the standard p-family condition: polynomially many variables *and*
  polynomially bounded total degree;
* `Formula.totalDegree_eval_le` — `deg(f) ≤ size(f)` for an arithmetic formula, hence
  `VPe.isPFamily`: every family entering `VP_e` is a standard p-family;
* `AffineHypercubeRep.totalDegree_value_le` — a product of `M` affine forms has degree at
  most `M`, and Boolean-hypercube summation does not raise the maximal degree in the
  original variables, hence `VNP1.isPFamily` (and its `VNP1LE3`, `VNP1LE2` corollaries):
  every family entering the affine-product hypercube classes — in particular every family
  used in the reverse containment `VNP₁^{[≤2]} ⊆ N(VP_e)` — is a standard p-family;
* `totalDegree_aeval_le` and `NondetClosure.isPFamily` — substituting variables by
  variables and Boolean constants does not raise the total degree, so the nondeterministic
  closure of a class of standard p-families again consists of standard p-families;
* the standard-p-family forms of the class theorem (`nondetVPe_eq_VNP1LE2_standard` and
  friends), which restrict the existing internal statements back to the standard
  literature universe.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.ClassLevelTwo

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial

variable {F : Type} [Field F]

/-! ## The standard p-family predicate -/

/-- The total degree of the `n`-th member of the family is polynomially bounded. -/
def PolyDegreeBounded (f : PolyFamily F) : Prop :=
  PolyBounded fun n => (f.poly n).totalDegree

/-- **The standard p-family condition** of the algebraic-complexity literature: the number
of variables and the total degree of the `n`-th member are both polynomially bounded. -/
def IsPFamily (f : PolyFamily F) : Prop :=
  PolyBounded f.nvars ∧ PolyDegreeBounded f

theorem IsPFamily.nvars {f : PolyFamily F} (h : IsPFamily f) : PolyBounded f.nvars := h.1

theorem IsPFamily.degree {f : PolyFamily F} (h : IsPFamily f) : PolyDegreeBounded f := h.2

/-! ## Degree of a formula -/

namespace Formula

variable {ι : Type}

/-- **`deg(f) ≤ size(f)`** for every binary division-free arithmetic formula. -/
theorem totalDegree_eval_le (f : Formula ι F) : (f.eval).totalDegree ≤ f.size := by
  induction f with
  | var i =>
      show (X i : MvPolynomial ι F).totalDegree ≤ _
      rw [totalDegree_X]
      show 1 ≤ 1 + 0 + 0
      omega
  | const c =>
      show (C c : MvPolynomial ι F).totalDegree ≤ _
      rw [totalDegree_C]
      exact Nat.zero_le _
  | add p q ihp ihq =>
      have hsize : (Formula.add p q).size = p.size + q.size + 1 := by
        show p.leaves + q.leaves + (p.addGates + q.addGates + 1) + (p.mulGates + q.mulGates)
          = _
        show _ = (p.leaves + p.addGates + p.mulGates) + (q.leaves + q.addGates + q.mulGates) + 1
        omega
      rw [hsize]
      show (p.eval + q.eval).totalDegree ≤ _
      exact le_trans (totalDegree_add _ _) (max_le (by omega) (by omega))
  | mul p q ihp ihq =>
      have hsize : (Formula.mul p q).size = p.size + q.size + 1 := by
        show p.leaves + q.leaves + (p.addGates + q.addGates) + (p.mulGates + q.mulGates + 1)
          = _
        show _ = (p.leaves + p.addGates + p.mulGates) + (q.leaves + q.addGates + q.mulGates) + 1
        omega
      rw [hsize]
      show (p.eval * q.eval).totalDegree ≤ _
      exact le_trans (totalDegree_mul _ _) (by omega)

end Formula

/-- **Every family in `VP_e` is a standard p-family.** -/
theorem VPe.polyDegreeBounded {f : PolyFamily F} (hf : VPe f) : PolyDegreeBounded f := by
  obtain ⟨-, φ, s, hs, hφ⟩ := hf
  refine PolyBounded.mono (fun n => ?_) hs
  have h1 : ((φ n).eval).totalDegree ≤ (φ n).size := Formula.totalDegree_eval_le _
  rw [(hφ n).1] at h1
  exact le_trans h1 (hφ n).2

theorem VPe.isPFamily {f : PolyFamily F} (hf : VPe f) : IsPFamily f :=
  ⟨hf.1, hf.polyDegreeBounded⟩

/-! ## Degree of an affine-product hypercube representation -/

namespace AffineForm

variable {σ ι : Type}

/-- An affine form evaluated at polynomials of degree at most one has degree at most one. -/
theorem totalDegree_eval_le_one (A : AffineForm σ F) (g : σ → MvPolynomial ι F)
    (hg : ∀ i, (g i).totalDegree ≤ 1) : (A.eval g).totalDegree ≤ 1 := by
  unfold eval
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · rw [algebraMap_eq, totalDegree_C]; exact Nat.zero_le _
  · induction A.terms with
    | nil => simp
    | cons p l ih =>
        rw [List.map_cons, List.sum_cons]
        refine le_trans (totalDegree_add _ _) (max_le ?_ ih)
        refine le_trans (totalDegree_mul _ _) ?_
        have hc : (algebraMap F (MvPolynomial ι F) p.1).totalDegree = 0 := by
          rw [algebraMap_eq, totalDegree_C]
        have := hg p.2
        omega

end AffineForm

namespace AffineHypercubeRep

variable {ι : Type}

theorem totalDegree_subst_le_one (R : AffineHypercubeRep ι F) (u : R.aux → Bool)
    (c : ι ⊕ R.aux) : ((R.subst u) c).totalDegree ≤ 1 := by
  rcases c with i | a
  · show (X i : MvPolynomial ι F).totalDegree ≤ 1
    rw [totalDegree_X]
  · show ((boolVal (u a) : MvPolynomial ι F)).totalDegree ≤ 1
    cases u a
    · show (0 : MvPolynomial ι F).totalDegree ≤ 1
      rw [totalDegree_zero]; omega
    · show (1 : MvPolynomial ι F).totalDegree ≤ 1
      rw [totalDegree_one]; omega

/-- **A product of `M` affine factors has total degree at most `M`, and summing over the
Boolean hypercube does not increase the maximal degree in the original variables.** -/
theorem totalDegree_value_le (R : AffineHypercubeRep ι F) :
    R.value.totalDegree ≤ R.numFactors := by
  classical
  show (∑ u : R.aux → Bool,
    (R.factors.map fun A : AffineForm (ι ⊕ R.aux) F => A.eval (R.subst u)).prod).totalDegree ≤ _
  refine MvPolynomial.totalDegree_finsetSum_le fun u _ => ?_
  refine le_trans (totalDegree_list_prod _) ?_
  have key : ∀ l : List (AffineForm (ι ⊕ R.aux) F),
      (((l.map fun A => A.eval (R.subst u)).map MvPolynomial.totalDegree).sum) ≤ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons A l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have := A.totalDegree_eval_le_one (R.subst u) (R.totalDegree_subst_le_one u)
        omega
  exact key R.factors

end AffineHypercubeRep

/-- **Every family in `VNP₁` is a standard p-family**: the degree is bounded by the number
of affine factors. -/
theorem VNP1.polyDegreeBounded {f : PolyFamily F} (hf : VNP1 f) : PolyDegreeBounded f := by
  obtain ⟨-, R, q, M, -, hM, h⟩ := hf
  refine PolyBounded.mono (fun n => ?_) hM
  have h1 : (R n).value.totalDegree ≤ (R n).numFactors :=
    AffineHypercubeRep.totalDegree_value_le _
  rw [show (R n).value = f.poly n from (h n).1] at h1
  exact le_trans h1 (h n).2.2

theorem VNP1.isPFamily {f : PolyFamily F} (hf : VNP1 f) : IsPFamily f :=
  ⟨hf.1, hf.polyDegreeBounded⟩

theorem VNP1LE3.isPFamily {f : PolyFamily F} (hf : VNP1LE3 f) : IsPFamily f :=
  hf.toVNP1.isPFamily

theorem VNP1LE2.isPFamily {f : PolyFamily F} (hf : VNP1LE2 f) : IsPFamily f :=
  hf.toVNP1LE3.isPFamily

/-! ## The nondeterministic closure preserves the standard p-family condition -/

/-- Substituting every variable by a polynomial of degree at most one does not raise the
total degree. -/
theorem totalDegree_aeval_le {σ ι : Type} (g : σ → MvPolynomial ι F)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial σ F) :
    (aeval g p).totalDegree ≤ p.totalDegree := by
  classical
  rw [show aeval g p = eval₂ (algebraMap F (MvPolynomial ι F)) g p from rfl, eval₂_eq]
  refine MvPolynomial.totalDegree_finsetSum_le fun d hd => ?_
  refine le_trans (totalDegree_mul _ _) ?_
  have hC : (algebraMap F (MvPolynomial ι F) (coeff d p)).totalDegree = 0 := by
    rw [algebraMap_eq, totalDegree_C]
  have hprod : (∏ i ∈ d.support, g i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
    refine le_trans (totalDegree_finset_prod _ _) (Finset.sum_le_sum fun i _ => ?_)
    calc (g i ^ d i).totalDegree ≤ d i * (g i).totalDegree := totalDegree_pow _ _
      _ ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
      _ = d i := mul_one _
  have hle : (∑ i ∈ d.support, d i) ≤ p.totalDegree := by
    simpa [Finsupp.sum] using MvPolynomial.le_totalDegree hd
  omega

theorem totalDegree_witnessSubst_le_one {m k N : ℕ} (b : Fin k → Bool) (i : Fin N) :
    ((witnessSubst (F := F) m k b) i).totalDegree ≤ 1 := by
  unfold witnessSubst
  by_cases hm : (i : ℕ) < m
  · rw [dif_pos hm, totalDegree_X]
  · rw [dif_neg hm]
    by_cases hk : (i : ℕ) - m < k
    · rw [dif_pos hk]
      cases b ⟨(i : ℕ) - m, hk⟩
      · show (0 : MvPolynomial (Fin m) F).totalDegree ≤ 1
        rw [totalDegree_zero]; omega
      · show (1 : MvPolynomial (Fin m) F).totalDegree ≤ 1
        rw [totalDegree_one]; omega
    · rw [dif_neg hk, totalDegree_zero]; omega

/-- **The nondeterministic closure of a class of standard p-families consists of standard
p-families**: Boolean witness summation substitutes variables by variables and constants,
which does not raise the total degree. -/
theorem NondetClosure.polyDegreeBounded {C : PolyFamily F → Prop} {f : PolyFamily F}
    (hC : ∀ g, C g → PolyDegreeBounded g) (hf : NondetClosure C f) : PolyDegreeBounded f := by
  obtain ⟨-, g, p, q, hg, -, hq, hrep⟩ := hf
  have hdeg : PolyBounded fun n => (g.poly (q n)).totalDegree :=
    PolyBounded.comp (hC g hg) hq
  refine PolyBounded.mono (fun n => ?_) hdeg
  rw [(hrep n).2]
  refine MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
  exact totalDegree_aeval_le _ (totalDegree_witnessSubst_le_one b) _

theorem NondetClosure.isPFamily {C : PolyFamily F → Prop} {f : PolyFamily F}
    (hC : ∀ g, C g → PolyDegreeBounded g) (hf : NondetClosure C f) : IsPFamily f :=
  ⟨hf.1, NondetClosure.polyDegreeBounded hC hf⟩

/-- Every family in `N(VP_e)` is a standard p-family. -/
theorem nondetVPe_isPFamily {f : PolyFamily F} (hf : NondetClosure VPe f) : IsPFamily f :=
  NondetClosure.isPFamily (fun _ hg => VPe.polyDegreeBounded hg) hf

/-! ## Standard-p-family forms of the class theorems -/

/-- **The class equality restricted to the standard literature universe.**  Both sides of
the internal equality `N(VP_e(F)) = VNP₁^{[≤2]}(F)` consist of standard p-families, so the
equality holds verbatim inside the standard p-family universe. -/
theorem nondetVPe_eq_VNP1LE2_standard [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (fun f : PolyFamily F => NondetClosure VPe f ∧ IsPFamily f)
      = fun f : PolyFamily F => VNP1LE2 f ∧ IsPFamily f := by
  funext f
  refine propext ⟨fun h => ⟨nondetVPe_subset_VNP1LE2 hτ0 hτ1 h.1, h.2⟩,
    fun h => ⟨VNP1LE2_subset_nondetVPe h.1, h.2⟩⟩

/-- The standard-p-family condition is automatic on both sides of the class equality. -/
theorem nondetVPe_iff_VNP1LE2_isPFamily [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    (f : PolyFamily F) :
    (NondetClosure VPe f ∧ IsPFamily f) ↔ (VNP1LE2 f ∧ IsPFamily f) := by
  refine ⟨fun h => ⟨nondetVPe_subset_VNP1LE2 hτ0 hτ1 h.1, h.2⟩,
    fun h => ⟨VNP1LE2_subset_nondetVPe h.1, h.2⟩⟩

/-- The forward containment in standard-p-family form: every standard p-family in
`N(VP_e(F))` lies in `VNP₁^{[≤2]}(F)`, and is again a standard p-family. -/
theorem nondetVPe_subset_VNP1LE2_standard [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : NondetClosure VPe f) : VNP1LE2 f ∧ IsPFamily f :=
  ⟨nondetVPe_subset_VNP1LE2 hτ0 hτ1 hf, nondetVPe_isPFamily hf⟩

/-- The reverse containment in standard-p-family form. -/
theorem VNP1LE2_subset_nondetVPe_standard {f : PolyFamily F} (hf : VNP1LE2 f) :
    NondetClosure VPe f ∧ IsPFamily f :=
  ⟨VNP1LE2_subset_nondetVPe hf, hf.isPFamily⟩

/-- `VP_e ⊆ VNP₁^{[≤2]}` in standard-p-family form. -/
theorem VPe_subset_VNP1LE2_standard [CharP F 2] {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    {f : PolyFamily F} (hf : VPe f) : VNP1LE2 f ∧ IsPFamily f :=
  ⟨VPe_subset_VNP1LE2 hτ0 hτ1 hf, hf.isPFamily⟩

end VNP1Char2
