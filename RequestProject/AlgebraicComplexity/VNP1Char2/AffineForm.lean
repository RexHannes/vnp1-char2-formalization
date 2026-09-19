/-
# Affine forms and affine-product hypercube representations

An `AffineForm σ F` is a constant plus an explicit finite list of `(coefficient, variable)`
terms.  Working with an explicit list (rather than with a polynomial together with a proof
that it is affine) makes the *support* of a factor — the number of variables it actually
mentions — completely transparent: `numVars` is the length of the list, and `vars` is the
finset of variables occurring in it, with `vars.card ≤ numVars`.

An `AffineHypercubeRep ι F` is a finite list of affine forms in the original variables
`ι` together with a finite set `aux` of Boolean auxiliaries; its `value` is

```
∑_{u : aux → Bool} ∏_j A_j(X, u).
```
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.BasicBoolean

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial

/-- An affine form: a constant term plus a list of coefficient/variable pairs. -/
structure AffineForm (σ : Type*) (F : Type*) where
  /-- the constant term -/
  const : F
  /-- the linear terms -/
  terms : List (F × σ)

namespace AffineForm

variable {σ F : Type*}

/-- The number of linear terms; an upper bound for the number of variables occurring. -/
def numVars (A : AffineForm σ F) : ℕ := A.terms.length

@[simp] theorem numVars_mapVar' {σ' : Type*} (f : σ → σ') (A : AffineForm σ F) :
    (⟨A.const, A.terms.map fun p => (p.1, f p.2)⟩ : AffineForm σ' F).numVars = A.numVars := by
  simp [numVars]

/-- The variables occurring in an affine form. -/
def vars [DecidableEq σ] (A : AffineForm σ F) : Finset σ := (A.terms.map Prod.snd).toFinset

theorem card_vars_le [DecidableEq σ] (A : AffineForm σ F) : A.vars.card ≤ A.numVars := by
  refine le_trans (List.toFinset_card_le _) ?_
  simp [numVars]


section Eval

variable [CommRing F] {M : Type*} [CommRing M] [Algebra F M]

/-- Evaluation of an affine form at an assignment of ring elements to the variables. -/
def eval (A : AffineForm σ F) (g : σ → M) : M :=
  algebraMap F M A.const + (A.terms.map fun p => algebraMap F M p.1 * g p.2).sum

@[simp] theorem eval_const (c : F) (g : σ → M) :
    eval (⟨c, []⟩ : AffineForm σ F) g = algebraMap F M c := by simp [eval]

/-- The polynomial attached to an affine form. -/
noncomputable def toPoly (A : AffineForm σ F) : MvPolynomial σ F :=
  C A.const + (A.terms.map fun p => C p.1 * X p.2).sum

/-- Evaluating the associated polynomial is the same as evaluating the affine form. -/
theorem aeval_toPoly (A : AffineForm σ F) (g : σ → M) :
    aeval g A.toPoly = A.eval g := by
  unfold toPoly eval
  rw [map_add]
  congr 1
  · simp
  · induction A.terms with
    | nil => simp
    | cons p l ih => simp [ih]

end Eval

section Ops

variable [CommRing F] {M : Type*} [CommRing M] [Algebra F M] {σ' : Type*}

theorem sum_map_smul (c : F) (l : List (F × σ)) (g : σ → M) :
    (l.map fun p => algebraMap F M c * algebraMap F M p.1 * g p.2).sum
      = algebraMap F M c * (l.map fun p => algebraMap F M p.1 * g p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]; ring

/-- `scaleShift c A d extra` is the affine form `c * A + d + ∑ extra`. -/
def scaleShift (c : F) (A : AffineForm σ F) (d : F) (extra : List (F × σ)) : AffineForm σ F :=
  ⟨c * A.const + d, A.terms.map (fun p => (c * p.1, p.2)) ++ extra⟩

theorem eval_scaleShift (c : F) (A : AffineForm σ F) (d : F) (extra : List (F × σ))
    (g : σ → M) : (scaleShift c A d extra).eval g
      = algebraMap F M c * A.eval g + algebraMap F M d
        + (extra.map fun p => algebraMap F M p.1 * g p.2).sum := by
  unfold scaleShift eval
  simp only [map_add, map_mul, List.map_append, List.sum_append, List.map_map, Function.comp_def]
  rw [sum_map_smul]
  ring

@[simp] theorem numVars_scaleShift (c : F) (A : AffineForm σ F) (d : F) (extra : List (F × σ)) :
    (scaleShift c A d extra).numVars = A.numVars + extra.length := by
  simp [scaleShift, numVars]

/-- The affine form consisting of a single variable. -/
def varForm (i : σ) : AffineForm σ F := ⟨0, [(1, i)]⟩

@[simp] theorem eval_varForm (i : σ) (g : σ → M) : (varForm (F := F) i).eval g = g i := by
  simp [varForm, eval]

@[simp] theorem numVars_varForm (i : σ) : (varForm (F := F) i).numVars = 1 := rfl

/-- Renaming the variables of an affine form. -/
def mapVar (f : σ → σ') (A : AffineForm σ F) : AffineForm σ' F :=
  ⟨A.const, A.terms.map fun p => (p.1, f p.2)⟩

theorem eval_mapVar (f : σ → σ') (A : AffineForm σ F) (g : σ' → M) :
    (mapVar f A).eval g = A.eval (g ∘ f) := by
  simp [mapVar, eval, List.map_map, Function.comp_def]

end Ops

end AffineForm

/-- A finite affine-product Boolean-hypercube representation: a list of affine factors in
the original variables `ι` and the Boolean auxiliaries `aux`. -/
structure AffineHypercubeRep (ι : Type*) (F : Type*) where
  /-- the type of Boolean auxiliaries -/
  aux : Type
  /-- the auxiliaries form a finite set -/
  auxFintype : Fintype aux
  /-- equality of auxiliaries is decidable -/
  auxDecEq : DecidableEq aux
  /-- the affine factors -/
  factors : List (AffineForm (ι ⊕ aux) F)

attribute [instance] AffineHypercubeRep.auxFintype AffineHypercubeRep.auxDecEq

namespace AffineHypercubeRep

variable {ι F : Type*} [CommRing F]

/-- The number of summed Boolean variables, `q`. -/
def numAux (R : AffineHypercubeRep ι F) : ℕ := Fintype.card R.aux

/-- The number of affine factors, `M`. -/
def numFactors (R : AffineHypercubeRep ι F) : ℕ := R.factors.length

/-- Every factor mentions at most `n` variables. -/
def SupportLE (R : AffineHypercubeRep ι F) (n : ℕ) : Prop := ∀ A ∈ R.factors, A.numVars ≤ n

/-- The assignment substituting the original indeterminates and the Boolean values `u`. -/
noncomputable def subst (R : AffineHypercubeRep ι F) (u : R.aux → Bool) :
    (ι ⊕ R.aux) → MvPolynomial ι F :=
  Sum.elim X fun a => boolVal (u a)

/-- The polynomial represented: the Boolean-hypercube sum of the product of the factors. -/
noncomputable def value (R : AffineHypercubeRep ι F) : MvPolynomial ι F :=
  ∑ u : R.aux → Bool, (R.factors.map fun A => A.eval (R.subst u)).prod

/-- `R` represents `f`. -/
def Represents (R : AffineHypercubeRep ι F) (f : MvPolynomial ι F) : Prop := R.value = f

end AffineHypercubeRep

end VNP1Char2
