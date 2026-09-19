/-
# A minimal p-family glossary

This is a new, strictly append-only layer on top of the finite compiler.  Nothing in the
existing `VNP1Char2` files is modified, renamed, weakened or reproved.

The purpose of this file is to define *just enough* infrastructure to state the class-level
inclusion `VP_e(F) ⊆ VNP₁^{[≤3]}(F)` rigorously:

* `PolyBounded p` — an explicit elementary polynomial bound `p n ≤ c * (n+1)^k`, together
  with the handful of closure properties that the class arguments need;
* `PolyFamily F` — a sequence of multivariate polynomials, the `n`-th one in the variables
  `Fin (nvars n)`.  Using a *finite* variable index type per index `n` makes "polynomially
  many variables" a structural statement (`PolyBounded nvars`) rather than a side condition
  on variable names;
* `VPe` — families computed by arithmetic formulas of polynomially bounded size;
* `VNP1LE3` and `VNP1` — families admitting, for every `n`, an affine-product
  Boolean-hypercube representation (the object produced by the banked finite compiler),
  with polynomially bounded cube dimension and factor count, and — for `VNP1LE3` — with
  every affine factor of support at most three, the support being counted over *all*
  variables of the factor, original and hypercube alike.

The file also contains the two elementary translations used later:

* an affine form is a small arithmetic formula (`AffineForm.toFormula`), and a product of
  finitely many formulas is a formula (`Formula.prodList`), with exact size accounting;
* an affine-product representation may be reindexed along any renaming of its variables
  (`AffineHypercubeRep.reindex`), which is how a compiled representation is later merged
  with an outer witness cube.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.MainCompiler

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial AffineForm

/-! ## Polynomially bounded functions -/

/-- `PolyBounded p` : the function `p` is bounded by an explicit polynomial `c * (n+1)^k`. -/
def PolyBounded (p : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, p n ≤ c * (n + 1) ^ k

theorem polyBounded_const (c : ℕ) : PolyBounded fun _ => c := ⟨c, 0, fun _ => by simp⟩

theorem polyBounded_id : PolyBounded fun n => n := ⟨1, 1, fun n => by simp⟩

theorem PolyBounded.mono {p q : ℕ → ℕ} (h : ∀ n, p n ≤ q n) (hq : PolyBounded q) :
    PolyBounded p := by
  obtain ⟨c, k, hc⟩ := hq
  exact ⟨c, k, fun n => le_trans (h n) (hc n)⟩

theorem PolyBounded.add {p q : ℕ → ℕ} (hp : PolyBounded p) (hq : PolyBounded q) :
    PolyBounded fun n => p n + q n := by
  obtain ⟨c₁, k₁, h₁⟩ := hp
  obtain ⟨c₂, k₂, h₂⟩ := hq
  refine ⟨c₁ + c₂, max k₁ k₂, fun n => ?_⟩
  have e₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ max k₁ k₂ :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (le_max_left _ _)
  have e₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ max k₁ k₂ :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (le_max_right _ _)
  calc p n + q n ≤ c₁ * (n + 1) ^ k₁ + c₂ * (n + 1) ^ k₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ c₁ * (n + 1) ^ max k₁ k₂ + c₂ * (n + 1) ^ max k₁ k₂ :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e₁) (Nat.mul_le_mul_left _ e₂)
    _ = (c₁ + c₂) * (n + 1) ^ max k₁ k₂ := by ring

theorem PolyBounded.const_mul {p : ℕ → ℕ} (a : ℕ) (hp : PolyBounded p) :
    PolyBounded fun n => a * p n := by
  obtain ⟨c, k, hc⟩ := hp
  exact ⟨a * c, k, fun n => by
    calc a * p n ≤ a * (c * (n + 1) ^ k) := Nat.mul_le_mul_left _ (hc n)
      _ = a * c * (n + 1) ^ k := by ring⟩

theorem PolyBounded.comp {p q : ℕ → ℕ} (hp : PolyBounded p) (hq : PolyBounded q) :
    PolyBounded fun n => p (q n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hp
  obtain ⟨c₂, k₂, h₂⟩ := hq
  refine ⟨c₁ * (c₂ + 1) ^ k₁, k₁ * k₂, fun n => ?_⟩
  have hone : 1 ≤ (n + 1) ^ k₂ := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hstep : q n + 1 ≤ (c₂ + 1) * (n + 1) ^ k₂ := by
    have := h₂ n
    nlinarith [hone, this]
  calc p (q n) ≤ c₁ * (q n + 1) ^ k₁ := h₁ (q n)
    _ ≤ c₁ * ((c₂ + 1) * (n + 1) ^ k₂) ^ k₁ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep k₁)
    _ = c₁ * (c₂ + 1) ^ k₁ * (n + 1) ^ (k₁ * k₂) := by
        rw [mul_pow, ← pow_mul, mul_comm k₂ k₁]; ring

/-! ## Families of polynomials -/

/-- A family of multivariate polynomials: the `n`-th member has variables `Fin (nvars n)`. -/
structure PolyFamily (F : Type) [CommSemiring F] where
  /-- the number of variables of the `n`-th member -/
  nvars : ℕ → ℕ
  /-- the `n`-th polynomial -/
  poly : ∀ n, MvPolynomial (Fin (nvars n)) F

variable {F : Type} [Field F]

/-- **`VP_e`** (formula class): families computed by arithmetic formulas, with polynomially
bounded variable count and polynomially bounded formula size. -/
def VPe (f : PolyFamily F) : Prop :=
  PolyBounded f.nvars ∧
    ∃ (φ : ∀ n, Formula (Fin (f.nvars n)) F) (s : ℕ → ℕ),
      PolyBounded s ∧ ∀ n, (φ n).eval = f.poly n ∧ (φ n).size ≤ s n

/-- **`VNP₁^{[≤3]}`**: families admitting, for every `n`, an affine-product Boolean-hypercube
representation with polynomially bounded cube dimension `q n` and factor count `M n`, in
which every affine factor has support at most three (counted over original *and* hypercube
variables). -/
def VNP1LE3 (f : PolyFamily F) : Prop :=
  PolyBounded f.nvars ∧
    ∃ (R : ∀ n, AffineHypercubeRep (Fin (f.nvars n)) F) (q M : ℕ → ℕ),
      PolyBounded q ∧ PolyBounded M ∧
        ∀ n, (R n).Represents (f.poly n) ∧ (R n).SupportLE 3 ∧
          (R n).numAux ≤ q n ∧ (R n).numFactors ≤ M n

/-- **`VNP₁`**: as `VNP1LE3` but with no support restriction on the affine factors. -/
def VNP1 (f : PolyFamily F) : Prop :=
  PolyBounded f.nvars ∧
    ∃ (R : ∀ n, AffineHypercubeRep (Fin (f.nvars n)) F) (q M : ℕ → ℕ),
      PolyBounded q ∧ PolyBounded M ∧
        ∀ n, (R n).Represents (f.poly n) ∧
          (R n).numAux ≤ q n ∧ (R n).numFactors ≤ M n

theorem VNP1LE3.toVNP1 {f : PolyFamily F} (h : VNP1LE3 f) : VNP1 f := by
  obtain ⟨hv, R, q, M, hq, hM, h⟩ := h
  exact ⟨hv, R, q, M, hq, hM, fun n => ⟨(h n).1, (h n).2.2.1, (h n).2.2.2⟩⟩

/-! ## Affine forms as small formulas -/

namespace AffineForm

variable {ι : Type}

/-- An affine form, read as an arithmetic formula. -/
def toFormula (A : AffineForm ι F) : Formula ι F :=
  A.terms.foldr (fun p acc => .add (.mul (.const p.1) (.var p.2)) acc) (.const A.const)

theorem toFormula_eval (A : AffineForm ι F) : (A.toFormula).eval = A.toPoly := by
  unfold toFormula toPoly
  induction A.terms with
  | nil => simp [Formula.eval]
  | cons p l ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, Formula.eval] at *
      rw [ih]; ring

omit [Field F] in
theorem toFormula_size (A : AffineForm ι F) : (A.toFormula).size = 4 * A.numVars + 1 := by
  unfold toFormula numVars
  induction A.terms with
  | nil => rfl
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons]
      show (Formula.add (Formula.mul (Formula.const p.1) (Formula.var p.2)) _).size = _
      simp only [Formula.size, Formula.leaves, Formula.addGates, Formula.mulGates] at *
      omega

end AffineForm

namespace Formula

variable {ι : Type}

/-- The product of a finite list of formulas. -/
def prodList : List (Formula ι F) → Formula ι F
  | [] => .const 1
  | f :: fs => .mul f (prodList fs)

theorem prodList_eval (l : List (Formula ι F)) :
    (prodList l).eval = (l.map Formula.eval).prod := by
  induction l with
  | nil => simp [prodList, Formula.eval]
  | cons f fs ih => simp [prodList, Formula.eval, ih]

theorem prodList_size (l : List (Formula ι F)) :
    (prodList l).size = (l.map fun f => f.size + 1).sum + 1 := by
  induction l with
  | nil => rfl
  | cons f fs ih =>
      show (Formula.mul f (prodList fs)).size = _
      simp only [Formula.size, Formula.leaves, Formula.addGates, Formula.mulGates] at *
      simp only [List.map_cons, List.sum_cons]
      omega

theorem prodList_size_le (l : List (Formula ι F)) (c : ℕ) (h : ∀ f ∈ l, f.size ≤ c) :
    (prodList l).size ≤ (c + 1) * l.length + 1 := by
  rw [prodList_size]
  have key : (l.map fun f => f.size + 1).sum ≤ (c + 1) * l.length := by
    induction l with
    | nil => simp
    | cons f fs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have h1 : f.size ≤ c := h f (List.mem_cons_self ..)
        have h2 := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
        calc f.size + 1 + (fs.map fun g => g.size + 1).sum
            ≤ (c + 1) + (c + 1) * fs.length := Nat.add_le_add (by omega) h2
          _ = (c + 1) * (fs.length + 1) := by ring
  omega

end Formula

/-! ## Homomorphisms and reindexing of affine data -/

namespace AffineForm

variable {σ : Type} {M N : Type} [CommRing M] [CommRing N] [Algebra F M] [Algebra F N]

/-- An `F`-algebra map commutes with evaluation of an affine form. -/
theorem map_eval (φ : M →ₐ[F] N) (A : AffineForm σ F) (g : σ → M) :
    φ (A.eval g) = A.eval (φ ∘ g) := by
  unfold eval
  rw [map_add, AlgHom.commutes]
  congr 1
  induction A.terms with
  | nil => simp
  | cons p l ih => simp [ih, map_add, map_mul, AlgHom.commutes]

variable {σ' : Type}

omit [Field F] in
@[simp] theorem numVars_mapVar (f : σ → σ') (A : AffineForm σ F) :
    (mapVar f A).numVars = A.numVars := by simp [mapVar, numVars]

end AffineForm

namespace AffineHypercubeRep

variable {ι ι' : Type}

/-- Reindexing an affine-product representation along a renaming of all its variables
(original and auxiliary), landing in a new set of auxiliaries. -/
def reindex (R : AffineHypercubeRep ι F) (A : Type) [Fintype A] [DecidableEq A]
    (ρ : ι ⊕ R.aux → ι' ⊕ A) : AffineHypercubeRep ι' F where
  aux := A
  auxFintype := inferInstance
  auxDecEq := inferInstance
  factors := R.factors.map (AffineForm.mapVar ρ)

omit [Field F] in
@[simp] theorem reindex_numAux (R : AffineHypercubeRep ι F) (A : Type) [Fintype A]
    [DecidableEq A] (ρ : ι ⊕ R.aux → ι' ⊕ A) :
    (R.reindex A ρ).numAux = Fintype.card A := rfl

omit [Field F] in
@[simp] theorem reindex_numFactors (R : AffineHypercubeRep ι F) (A : Type) [Fintype A]
    [DecidableEq A] (ρ : ι ⊕ R.aux → ι' ⊕ A) :
    (R.reindex A ρ).numFactors = R.numFactors := by
  simp [reindex, numFactors]

omit [Field F] in
theorem reindex_supportLE (R : AffineHypercubeRep ι F) (A : Type) [Fintype A] [DecidableEq A]
    (ρ : ι ⊕ R.aux → ι' ⊕ A) {n : ℕ} (h : R.SupportLE n) : (R.reindex A ρ).SupportLE n := by
  intro B hB
  simp only [reindex, List.mem_map] at hB
  obtain ⟨C, hC, rfl⟩ := hB
  rw [AffineForm.numVars_mapVar]
  exact h C hC

/-- The value of a reindexed representation: the factors are evaluated at the composite
assignment. -/
theorem reindex_value (R : AffineHypercubeRep ι F) (A : Type) [Fintype A] [DecidableEq A]
    (ρ : ι ⊕ R.aux → ι' ⊕ A) :
    (R.reindex A ρ).value =
      ∑ w : A → Bool,
        (R.factors.map fun B =>
          B.eval ((Sum.elim X fun a => boolVal (w a)) ∘ ρ)).prod := by
  unfold value reindex subst
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [List.map_map, Function.comp_def]
  exact congrArg List.prod (List.map_congr_left fun B _ => AffineForm.eval_mapVar ρ B _)

end AffineHypercubeRep

end VNP1Char2
