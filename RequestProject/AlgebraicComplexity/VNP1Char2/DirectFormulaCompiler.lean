/-
# The direct formula-tree activation compiler

A second, independent compiler from arithmetic formulas to affine-product Boolean-hypercube
representations with all affine factors of support at most two.  It does **not** use the
frozen graph/path layer: no DAG, no source–sink paths, no `inPairs`/`outPairs`, no
acyclicity, no cubic-error killing.  The only shared ingredients are the data types
(`Formula`, `AffineForm`, `AffineHypercubeRep`) and the one-bit three-factor `1 + x y`
gadget `gadget2Factors`, together with the new branch gadget of `DirectBranchGadget.lean`.

## The construction

Every syntax node `v` of the formula gets a fresh Boolean *activation* bit `z_v`.  Reading
the tree top-down:

* the **root** is pinned active by the unary affine factor `z_root`;
* a **multiplication** node `v = u · w` contributes the two affine factors `1 + z_v + z_u`
  and `1 + z_v + z_w`; on Boolean values in characteristic two `1 + x + y` is `1` if
  `x = y` and `0` otherwise, so both children inherit the parent's activation;
* an **addition** node `v = u + w` contributes the six-factor branch gadget of
  `DirectBranchGadget.lean` with `a = z_u`, `b = z_w`, `c = z_v` and one fresh auxiliary
  bit: an inactive parent forces both children inactive, an active parent activates exactly
  one child;
* a **leaf** with label `ℓ` contributes `1 + z_v (ℓ + 1)`, expanded by the banked
  three-factor support-two gadget `gadget2Factors` with `x = ℓ + 1`, `y = z_v` and one
  fresh auxiliary bit: the contribution is `1` when `z_v = 0` and `ℓ` when `z_v = 1`.

Freshness is literal: the auxiliary index type `Aux f` is built by structural recursion out
of disjoint sums, so distinct gadget occurrences own distinct coordinates even when two
equal-shaped subformulas occur.

## The semantic theorem

`condZ τ f b` is the conditioned partition function of the subtree `f` whose root
activation bit is pinned to `b`.  The main induction is

```
condZ τ f false = 1,      condZ τ f true = f.eval,          (SEM)
```

an identity of *polynomials in the original formula variables*; only activation and gadget
auxiliaries are Boolean-summed.  Pinning the root then gives
`(directRep τ f).value = f.eval`.

## Size

`q = numAux = 2l + 2a + u ≤ 2 s` and `M = numFactors = 1 + 3l + 6a + 2u`, with
`2M ≤ 9 s` and `M ≤ 5 s`, where `l, a, u` are the numbers of leaves, addition gates and
multiplication gates and `s = l + a + u`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.DirectBranchGadget
import RequestProject.AlgebraicComplexity.VNP1Char2.FormulaToDAG

namespace VNP1Char2

open scoped BigOperators
open AffineForm MvPolynomial

/-! ## Boolean-cube splitting helpers

These are the flattening lemmas used to turn the nested Boolean sums of the recursion into
a single hypercube sum.  Nothing here identifies the auxiliaries of two gadgets: each
splitting is along a *disjoint sum* of index types. -/

section Cube

variable {M : Type*} [CommRing M]

/-- The Boolean cube over a disjoint union splits into a double sum. -/
theorem sum_cube_sum {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : (A ⊕ B → Bool) → M) :
    (∑ u : (A ⊕ B) → Bool, G u) = ∑ ua : A → Bool, ∑ ub : B → Bool, G (Sum.elim ua ub) := by
  rw [← Equiv.sum_comp (Equiv.sumArrowEquivProdArrow A B Bool).symm G, Fintype.sum_prod_type]
  rfl

/-- The Boolean cube over `Unit ⊕ A` splits into the value of the distinguished bit and the
cube over `A`. -/
theorem sum_cube_unit {A : Type} [Fintype A] [DecidableEq A] (G : (Unit ⊕ A → Bool) → M) :
    (∑ u : (Unit ⊕ A) → Bool, G u)
      = ∑ b : Bool, ∑ v : A → Bool, G (Sum.elim (fun _ => b) v) := by
  rw [sum_cube_sum]
  refine Fintype.sum_equiv (Equiv.funUnique Unit Bool) _ _ fun ua => ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1

/-- Splitting a double cube sum whose summand factors into a product. -/
theorem sum_prod_split {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (Pa : (A → Bool) → M) (Pb : (B → Bool) → M) (ca : (A → Bool) → M) (cb : (B → Bool) → M) :
    (∑ ua : A → Bool, ∑ ub : B → Bool, ca ua * cb ub * (Pa ua * Pb ub))
      = (∑ ua : A → Bool, ca ua * Pa ua) * (∑ ub : B → Bool, cb ub * Pb ub) := by
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun ua _ => Finset.sum_congr rfl fun ub _ => by ring

/-- **The false step is never used.**  On Boolean values in characteristic two,
`1 + x + y` is the equality indicator. -/
theorem one_add_boolVal_add_boolVal (h2 : (2 : M) = 0) (x y : Bool) :
    (1 : M) + boolVal x + boolVal y = if x = y then 1 else 0 := by
  cases x <;> cases y <;> simp [boolVal] <;> linear_combination h2

end Cube

namespace Formula

variable {ι F : Type} [Field F]

/-! ## Fresh auxiliary coordinates, by structural recursion -/

/-- The auxiliary Boolean coordinates strictly *inside* a subtree: all activation bits
except the subtree's own root activation bit, and all gadget bits.  Distinct occurrences
live in distinct summands, so freshness holds by construction. -/
def Aux : Formula ι F → Type
  | .var _ => Unit
  | .const _ => Unit
  | .add p q => Unit ⊕ ((Unit ⊕ Aux p) ⊕ (Unit ⊕ Aux q))
  | .mul p q => (Unit ⊕ Aux p) ⊕ (Unit ⊕ Aux q)

/-- `Aux` is finite. -/
def auxFintype : (f : Formula ι F) → Fintype (Aux f)
  | .var _ => inferInstanceAs (Fintype Unit)
  | .const _ => inferInstanceAs (Fintype Unit)
  | .add p q => by
      letI := auxFintype p; letI := auxFintype q
      exact inferInstanceAs (Fintype (Unit ⊕ ((Unit ⊕ Aux p) ⊕ (Unit ⊕ Aux q))))
  | .mul p q => by
      letI := auxFintype p; letI := auxFintype q
      exact inferInstanceAs (Fintype ((Unit ⊕ Aux p) ⊕ (Unit ⊕ Aux q)))

/-- Equality of auxiliary coordinates is decidable. -/
def auxDecEq : (f : Formula ι F) → DecidableEq (Aux f)
  | .var _ => inferInstanceAs (DecidableEq Unit)
  | .const _ => inferInstanceAs (DecidableEq Unit)
  | .add p q => by
      letI := auxDecEq p; letI := auxDecEq q
      exact inferInstanceAs (DecidableEq (Unit ⊕ ((Unit ⊕ Aux p) ⊕ (Unit ⊕ Aux q))))
  | .mul p q => by
      letI := auxDecEq p; letI := auxDecEq q
      exact inferInstanceAs (DecidableEq ((Unit ⊕ Aux p) ⊕ (Unit ⊕ Aux q)))

instance instFintypeAux (f : Formula ι F) : Fintype (Aux f) := auxFintype f
instance instDecEqAux (f : Formula ι F) : DecidableEq (Aux f) := auxDecEq f

/-- The full auxiliary index type of a subtree: its root activation bit together with the
inner auxiliaries. -/
abbrev TAux (f : Formula ι F) : Type := Unit ⊕ Aux f

omit [Field F] in
/-- **Exact auxiliary count**: `q = 2l + 2a + u`, one activation bit per node plus one
gadget bit per leaf and per addition gate. -/
theorem card_taux : ∀ f : Formula ι F,
    Fintype.card (TAux f) = 2 * f.leaves + 2 * f.addGates + f.mulGates
  | .var _ => rfl
  | .const _ => rfl
  | .add p q => by
      have hp := card_taux p
      have hq := card_taux q
      show Fintype.card (Unit ⊕ (Unit ⊕ ((Unit ⊕ Aux p) ⊕ (Unit ⊕ Aux q)))) = _
      simp only [Fintype.card_sum, Fintype.card_unit] at *
      simp only [leaves, addGates, mulGates]
      omega
  | .mul p q => by
      have hp := card_taux p
      have hq := card_taux q
      show Fintype.card (Unit ⊕ ((Unit ⊕ Aux p) ⊕ (Unit ⊕ Aux q))) = _
      simp only [Fintype.card_sum, Fintype.card_unit] at *
      simp only [leaves, addGates, mulGates]
      omega

omit [Field F] in
/-- A binary tree has one more leaf than it has gates. -/
theorem leaves_eq_gates_succ : ∀ f : Formula ι F, f.leaves = f.addGates + f.mulGates + 1
  | .var _ => rfl
  | .const _ => rfl
  | .add p q => by
      have hp := leaves_eq_gates_succ p
      have hq := leaves_eq_gates_succ q
      simp only [leaves, addGates, mulGates] at *
      omega
  | .mul p q => by
      have hp := leaves_eq_gates_succ p
      have hq := leaves_eq_gates_succ q
      simp only [leaves, addGates, mulGates] at *
      omega

/-! ## The factors of the direct compiler -/

/-- The affine factors attached to the nodes of a subtree, *excluding* the root pin.  The
root activation bit of the subtree is the `Unit` component of `TAux`. -/
noncomputable def bodyFactors (τ : F) : (f : Formula ι F) → List (AffineForm (ι ⊕ TAux f) F)
  | .var i =>
      gadget2Factors τ ⟨1, [(1, Sum.inl i)]⟩ (varForm (Sum.inr (Sum.inl ())))
        (Sum.inr (Sum.inr ()))
  | .const c =>
      gadget2Factors τ ⟨c + 1, []⟩ (varForm (Sum.inr (Sum.inl ())))
        (Sum.inr (Sum.inr ()))
  | .add p q =>
      branchFactors τ (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ())))))
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
          (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inr (Sum.inl ())))
        ++ ((bodyFactors τ p).map
              (mapVar (Sum.map id fun t => Sum.inr (Sum.inr (Sum.inl t))))
            ++ (bodyFactors τ q).map
              (mapVar (Sum.map id fun t => Sum.inr (Sum.inr (Sum.inr t)))))
  | .mul p q =>
      [ ⟨1, [(1, Sum.inr (Sum.inl ())), (1, Sum.inr (Sum.inr (Sum.inl (Sum.inl ()))))]⟩,
        ⟨1, [(1, Sum.inr (Sum.inl ())), (1, Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))]⟩ ]
        ++ ((bodyFactors τ p).map (mapVar (Sum.map id fun t => Sum.inr (Sum.inl t)))
            ++ (bodyFactors τ q).map (mapVar (Sum.map id fun t => Sum.inr (Sum.inr t))))

/-- **Exact factor count of the body**: `3l + 6a + 2u`. -/
theorem length_bodyFactors (τ : F) : ∀ f : Formula ι F,
    (bodyFactors τ f).length = 3 * f.leaves + 6 * f.addGates + 2 * f.mulGates
  | .var _ => rfl
  | .const _ => rfl
  | .add p q => by
      have hp := length_bodyFactors τ p
      have hq := length_bodyFactors τ q
      simp only [bodyFactors, List.length_append, List.length_map, length_branchFactors,
        hp, hq, leaves, addGates, mulGates]
      omega
  | .mul p q => by
      have hp := length_bodyFactors τ p
      have hq := length_bodyFactors τ q
      simp only [bodyFactors, List.length_append, List.length_map, hp, hq,
        leaves, addGates, mulGates, List.length_cons, List.length_nil]
      omega

/-- **Support two for the body.**  Every affine factor produced by the direct compiler
mentions at most two variables. -/
theorem numVars_bodyFactors_le (τ : F) : ∀ (f : Formula ι F) (A : AffineForm (ι ⊕ TAux f) F),
    A ∈ bodyFactors τ f → A.numVars ≤ 2
  | .var i, A, hA => by
      have := numVars_gadget2Factors_le (τ := τ) (x := (⟨1, [(1, Sum.inl i)]⟩ :
        AffineForm (ι ⊕ TAux (Formula.var (F := F) i)) F))
        (y := varForm (Sum.inr (Sum.inl ()))) (hIdx := Sum.inr (Sum.inr ())) hA
      simpa [numVars, varForm] using this
  | .const c, A, hA => by
      have := numVars_gadget2Factors_le (τ := τ) (x := (⟨c + 1, []⟩ :
        AffineForm (ι ⊕ TAux (Formula.const (ι := ι) c)) F))
        (y := varForm (Sum.inr (Sum.inl ()))) (hIdx := Sum.inr (Sum.inr ())) hA
      simpa [numVars, varForm] using this
  | .add p q, A, hA => by
      simp only [bodyFactors, List.mem_append, List.mem_map] at hA
      rcases hA with h | h | h
      · exact numVars_branchFactors_le h
      · obtain ⟨B, hB, rfl⟩ := h
        simpa [mapVar, numVars] using numVars_bodyFactors_le τ p B hB
      · obtain ⟨B, hB, rfl⟩ := h
        simpa [mapVar, numVars] using numVars_bodyFactors_le τ q B hB
  | .mul p q, A, hA => by
      simp only [bodyFactors, List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false] at hA
      rcases hA with (rfl | rfl) | h | h
      · simp [numVars]
      · simp [numVars]
      · obtain ⟨B, hB, rfl⟩ := h
        simpa [mapVar, numVars] using numVars_bodyFactors_le τ p B hB
      · obtain ⟨B, hB, rfl⟩ := h
        simpa [mapVar, numVars] using numVars_bodyFactors_le τ q B hB

/-! ## The conditioned partition function -/

/-- The assignment sending the original variables to indeterminates and the auxiliaries of
`f` to their Boolean values. -/
noncomputable def substT (f : Formula ι F) (u : TAux f → Bool) :
    (ι ⊕ TAux f) → MvPolynomial ι F :=
  Sum.elim X fun t => boolVal (u t)

/-- The product of all body factors of `f` at a Boolean assignment of its auxiliaries. -/
noncomputable def bodyProd (τ : F) (f : Formula ι F) (u : TAux f → Bool) :
    MvPolynomial ι F :=
  ((bodyFactors τ f).map fun A => A.eval (substT f u)).prod

/-- **The conditioned partition function** of the subtree `f`, with its root activation bit
pinned to `b` and all inner auxiliaries summed over the Boolean cube. -/
noncomputable def condZ (τ : F) (f : Formula ι F) (b : Bool) : MvPolynomial ι F :=
  ∑ v : Aux f → Bool, bodyProd τ f (Sum.elim (fun _ => b) v)

/-- Pinning the root bit inside a cube sum. -/
theorem sum_pinned (τ : F) (g : Formula ι F) (b : Bool)
    (c : (TAux g → Bool) → MvPolynomial ι F)
    (hc : ∀ u : TAux g → Bool, c u = if u (Sum.inl ()) = b then 1 else 0) :
    (∑ u : TAux g → Bool, c u * bodyProd τ g u) = condZ τ g b := by
  simp_rw [hc]
  rw [sum_cube_unit (fun u => (if u (Sum.inl ()) = b then 1 else 0) * bodyProd τ g u)]
  cases b <;> simp [condZ]

/-- Child factors, embedded and evaluated, are the child's own factors evaluated at the
restricted assignment. -/
theorem bodyProd_child (τ : F) {f g : Formula ι F} (ρ : TAux g → TAux f)
    (u : TAux f → Bool) (u' : TAux g → Bool) (h : ∀ t, u (ρ t) = u' t) :
    (((bodyFactors τ g).map (mapVar (Sum.map id ρ))).map fun A =>
        A.eval (substT f u)).prod = bodyProd τ g u' := by
  unfold bodyProd
  simp only [List.map_map, Function.comp_def]
  refine congrArg List.prod (List.map_congr_left fun A _ => ?_)
  rw [eval_mapVar]
  congr 1
  funext x
  rcases x with i | t
  · rfl
  · show boolVal (u (ρ t)) = boolVal (u' t)
    rw [h t]

/-! ## The semantic theorem (SEM) -/

variable [CharP F 2]

theorem condZ_var {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (i : ι) (b : Bool) :
    condZ τ (Formula.var (F := F) i) b
      = 1 + (1 + X i) * (boolVal b : MvPolynomial ι F) := by
  unfold condZ
  rw [show (∑ v : Aux (Formula.var (F := F) i) → Bool,
      bodyProd τ (Formula.var (F := F) i) (Sum.elim (fun _ => b) v))
      = ∑ h : Bool, bodyProd τ (Formula.var (F := F) i)
          (Sum.elim (fun _ => b) fun _ => h) from
    Fintype.sum_equiv (Equiv.funUnique Unit Bool) _ _ fun v => by congr 1]
  have hstep : ∀ h : Bool, bodyProd τ (Formula.var (F := F) i)
      (Sum.elim (fun _ => b) fun _ => h)
      = twoGadgetBody τ (1 + X i) (boolVal b) (boolVal h) := by
    intro h
    set g : (ι ⊕ TAux (Formula.var (F := F) i)) → MvPolynomial ι F :=
      substT (Formula.var (F := F) i) (Sum.elim (fun _ => b) fun _ => h) with hg
    have hx : (⟨1, [(1, Sum.inl i)]⟩ :
        AffineForm (ι ⊕ TAux (Formula.var (F := F) i)) F).eval g = 1 + X i := by
      simp [AffineForm.eval, hg, substT, MvPolynomial.algebraMap_eq]
    have hy : (varForm (F := F) (Sum.inr (Sum.inl ())) :
        AffineForm (ι ⊕ TAux (Formula.var (F := F) i)) F).eval g
        = (boolVal b : MvPolynomial ι F) := by
      simp [varForm, AffineForm.eval, hg, substT]
    unfold bodyProd bodyFactors
    rw [prod_gadget2Factors τ _ _ _ g h rfl, hx, hy]
  simp_rw [hstep]
  exact twoFactor_identity hτ0 hτ1 _ _

theorem condZ_const {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (c : F) (b : Bool) :
    condZ τ (Formula.const (ι := ι) c) b
      = 1 + (1 + C c) * (boolVal b : MvPolynomial ι F) := by
  unfold condZ
  rw [show (∑ v : Aux (Formula.const (ι := ι) c) → Bool,
      bodyProd τ (Formula.const (ι := ι) c) (Sum.elim (fun _ => b) v))
      = ∑ h : Bool, bodyProd τ (Formula.const (ι := ι) c)
          (Sum.elim (fun _ => b) fun _ => h) from
    Fintype.sum_equiv (Equiv.funUnique Unit Bool) _ _ fun v => by congr 1]
  have hstep : ∀ h : Bool, bodyProd τ (Formula.const (ι := ι) c)
      (Sum.elim (fun _ => b) fun _ => h)
      = twoGadgetBody τ (1 + C c) (boolVal b) (boolVal h) := by
    intro h
    set g : (ι ⊕ TAux (Formula.const (ι := ι) c)) → MvPolynomial ι F :=
      substT (Formula.const (ι := ι) c) (Sum.elim (fun _ => b) fun _ => h) with hg
    have hx : (⟨c + 1, []⟩ :
        AffineForm (ι ⊕ TAux (Formula.const (ι := ι) c)) F).eval g = 1 + C c := by
      simp [AffineForm.eval, hg, substT, MvPolynomial.algebraMap_eq]
      ring
    have hy : (varForm (F := F) (Sum.inr (Sum.inl ())) :
        AffineForm (ι ⊕ TAux (Formula.const (ι := ι) c)) F).eval g
        = (boolVal b : MvPolynomial ι F) := by
      simp [varForm, AffineForm.eval, hg, substT]
    unfold bodyProd bodyFactors
    rw [prod_gadget2Factors τ _ _ _ g h rfl, hx, hy]
  simp_rw [hstep]
  exact twoFactor_identity hτ0 hτ1 _ _

/-- **The multiplication rule.**  The two equality factors force both children to inherit
the parent's activation state. -/
theorem condZ_mul (τ : F) (p q : Formula ι F) (b : Bool) :
    condZ τ (Formula.mul p q) b = condZ τ p b * condZ τ q b := by
  have h2 : (2 : MvPolynomial ι F) = 0 := two_eq_zero_of_algebra F
  have hsplit : ∀ (up : TAux p → Bool) (uq : TAux q → Bool),
      bodyProd τ (Formula.mul p q) (Sum.elim (fun _ => b) (Sum.elim up uq))
        = (if up (Sum.inl ()) = b then 1 else 0) * (if uq (Sum.inl ()) = b then 1 else 0)
            * (bodyProd τ p up * bodyProd τ q uq) := by
    intro up uq
    have hp' := bodyProd_child τ (f := Formula.mul p q) (g := p)
      (fun t => Sum.inr (Sum.inl t)) (Sum.elim (fun _ => b) (Sum.elim up uq)) up fun _ => rfl
    have hq' := bodyProd_child τ (f := Formula.mul p q) (g := q)
      (fun t => Sum.inr (Sum.inr t)) (Sum.elim (fun _ => b) (Sum.elim up uq)) uq fun _ => rfl
    have hrel1 : (⟨1, [(1, Sum.inr (Sum.inl ())),
          (1, Sum.inr (Sum.inr (Sum.inl (Sum.inl ()))))]⟩ :
          AffineForm (ι ⊕ TAux (Formula.mul p q)) F).eval
            (substT (Formula.mul p q) (Sum.elim (fun _ => b) (Sum.elim up uq)))
        = if up (Sum.inl ()) = b then 1 else 0 := by
      rw [← one_add_boolVal_add_boolVal h2 (up (Sum.inl ())) b]
      simp only [AffineForm.eval, substT, Sum.elim_inr, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, map_one, one_mul, Sum.elim_inl]
      ring
    have hrel2 : (⟨1, [(1, Sum.inr (Sum.inl ())),
          (1, Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))]⟩ :
          AffineForm (ι ⊕ TAux (Formula.mul p q)) F).eval
            (substT (Formula.mul p q) (Sum.elim (fun _ => b) (Sum.elim up uq)))
        = if uq (Sum.inl ()) = b then 1 else 0 := by
      rw [← one_add_boolVal_add_boolVal h2 (uq (Sum.inl ())) b]
      simp only [AffineForm.eval, substT, Sum.elim_inr, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, map_one, one_mul, Sum.elim_inl]
      ring
    unfold bodyProd
    simp only [bodyFactors, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, hrel1, hrel2]
    rw [show ((List.map (fun A => AffineForm.eval A
          (substT (Formula.mul p q) (Sum.elim (fun _ => b) (Sum.elim up uq))))
        ((bodyFactors τ p).map (mapVar (Sum.map id fun t => Sum.inr (Sum.inl t))))).prod)
        = bodyProd τ p up from hp',
      show ((List.map (fun A => AffineForm.eval A
          (substT (Formula.mul p q) (Sum.elim (fun _ => b) (Sum.elim up uq))))
        ((bodyFactors τ q).map (mapVar (Sum.map id fun t => Sum.inr (Sum.inr t))))).prod)
        = bodyProd τ q uq from hq']
    simp only [bodyProd]
    ring
  unfold condZ
  rw [show (∑ v : Aux (Formula.mul p q) → Bool,
        bodyProd τ (Formula.mul p q) (Sum.elim (fun _ => b) v))
      = ∑ up : TAux p → Bool, ∑ uq : TAux q → Bool,
          bodyProd τ (Formula.mul p q) (Sum.elim (fun _ => b) (Sum.elim up uq)) from
    sum_cube_sum (fun v => bodyProd τ (Formula.mul p q) (Sum.elim (fun _ => b) v))]
  simp_rw [hsplit]
  rw [sum_prod_split (fun up => bodyProd τ p up) (fun uq => bodyProd τ q uq)
      (fun up => if up (Sum.inl ()) = b then 1 else 0)
      (fun uq => if uq (Sum.inl ()) = b then 1 else 0),
    sum_pinned τ p b _ (fun _ => rfl), sum_pinned τ q b _ (fun _ => rfl)]
  rfl

/-- **The addition rule.**  The branch gadget allows exactly the states
`parent 0 → children 00` and `parent 1 → children 10 or 01`. -/
theorem condZ_add {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) (p q : Formula ι F) (b : Bool) :
    condZ τ (Formula.add p q) b
      = (if b = false then condZ τ p false * condZ τ q false
          else condZ τ p true * condZ τ q false + condZ τ p false * condZ τ q true) := by
  have hbv : ∀ x : Bool,
      (boolVal x : MvPolynomial ι F) = algebraMap F (MvPolynomial ι F) (boolVal x) := by
    intro x; cases x <;> simp [boolVal]
  -- the product over the body factors of an addition node, at a split assignment
  have hfac : ∀ (h : Bool) (up : TAux p → Bool) (uq : TAux q → Bool),
      bodyProd τ (Formula.add p q)
          (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) (Sum.elim up uq)))
        = ((branchFactors τ (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ())))))
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
              (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inr (Sum.inl ())))).map fun A =>
            A.eval (substT (Formula.add p q)
              (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) (Sum.elim up uq))))).prod
          * (bodyProd τ p up * bodyProd τ q uq) := by
    intro h up uq
    have hp' := bodyProd_child τ (f := Formula.add p q) (g := p)
      (fun t => Sum.inr (Sum.inr (Sum.inl t)))
      (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) (Sum.elim up uq))) up fun _ => rfl
    have hq' := bodyProd_child τ (f := Formula.add p q) (g := q)
      (fun t => Sum.inr (Sum.inr (Sum.inr t)))
      (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) (Sum.elim up uq))) uq fun _ => rfl
    unfold bodyProd
    simp only [bodyFactors, List.map_append, List.prod_append]
    rw [show ((List.map (fun A => AffineForm.eval A
          (substT (Formula.add p q)
            (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) (Sum.elim up uq)))))
        ((bodyFactors τ p).map
          (mapVar (Sum.map id fun t => Sum.inr (Sum.inr (Sum.inl t)))))).prod)
        = bodyProd τ p up from hp',
      show ((List.map (fun A => AffineForm.eval A
          (substT (Formula.add p q)
            (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) (Sum.elim up uq)))))
        ((bodyFactors τ q).map
          (mapVar (Sum.map id fun t => Sum.inr (Sum.inr (Sum.inr t)))))).prod)
        = bodyProd τ q uq from hq']
    simp only [bodyProd]
    rfl
  -- summing the branch gadget over its fresh auxiliary gives the activation indicator
  have hsum : ∀ (up : TAux p → Bool) (uq : TAux q → Bool),
      (∑ h : Bool, bodyProd τ (Formula.add p q)
          (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) (Sum.elim up uq))))
        = (if BranchAllowed (up (Sum.inl ())) (uq (Sum.inl ())) b then 1 else 0)
            * (bodyProd τ p up * bodyProd τ q uq) := by
    intro up uq
    simp_rw [hfac]
    rw [← Finset.sum_mul]
    congr 1
    exact sum_prod_branchFactors hτ0 hτ1 _ _ _ _
      (fun h => substT (Formula.add p q)
        (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) (Sum.elim up uq))))
      (up (Sum.inl ())) (uq (Sum.inl ())) b
      (fun _ => hbv _) (fun _ => hbv _) (fun _ => hbv _) (fun _ => hbv _)
  -- flatten the cube of the addition node into the branch bit and the two child cubes
  have main : condZ τ (Formula.add p q) b
      = ∑ up : TAux p → Bool, ∑ uq : TAux q → Bool,
          (if BranchAllowed (up (Sum.inl ())) (uq (Sum.inl ())) b then 1 else 0)
            * (bodyProd τ p up * bodyProd τ q uq) := by
    unfold condZ
    rw [show (∑ v : Aux (Formula.add p q) → Bool,
          bodyProd τ (Formula.add p q) (Sum.elim (fun _ => b) v))
        = ∑ h : Bool, ∑ w : (TAux p ⊕ TAux q) → Bool,
            bodyProd τ (Formula.add p q)
              (Sum.elim (fun _ => b) (Sum.elim (fun _ => h) w)) from
      sum_cube_unit (fun v => bodyProd τ (Formula.add p q) (Sum.elim (fun _ => b) v))]
    simp_rw [sum_cube_sum (A := TAux p) (B := TAux q)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun up _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun uq _ => ?_
    exact hsum up uq
  rw [main]
  cases b
  · have hind : ∀ (up : TAux p → Bool) (uq : TAux q → Bool),
        (if BranchAllowed (up (Sum.inl ())) (uq (Sum.inl ())) false then
            (1 : MvPolynomial ι F) else 0)
          = (if up (Sum.inl ()) = false then 1 else 0)
              * (if uq (Sum.inl ()) = false then 1 else 0) := by
      intro up uq
      cases hu : up (Sum.inl ()) <;> cases hv : uq (Sum.inl ()) <;>
        simp [BranchAllowed]
    simp_rw [hind]
    rw [sum_prod_split (fun up => bodyProd τ p up) (fun uq => bodyProd τ q uq)
        (fun up => if up (Sum.inl ()) = false then 1 else 0)
        (fun uq => if uq (Sum.inl ()) = false then 1 else 0),
      sum_pinned τ p false _ (fun _ => rfl), sum_pinned τ q false _ (fun _ => rfl)]
    simp
  · have hind : ∀ (up : TAux p → Bool) (uq : TAux q → Bool),
        (if BranchAllowed (up (Sum.inl ())) (uq (Sum.inl ())) true then
            (1 : MvPolynomial ι F) else 0) * (bodyProd τ p up * bodyProd τ q uq)
          = (if up (Sum.inl ()) = true then 1 else 0)
              * (if uq (Sum.inl ()) = false then 1 else 0)
              * (bodyProd τ p up * bodyProd τ q uq)
            + (if up (Sum.inl ()) = false then 1 else 0)
              * (if uq (Sum.inl ()) = true then 1 else 0)
              * (bodyProd τ p up * bodyProd τ q uq) := by
      intro up uq
      cases hu : up (Sum.inl ()) <;> cases hv : uq (Sum.inl ()) <;>
        simp [BranchAllowed]
    simp_rw [hind, Finset.sum_add_distrib]
    rw [sum_prod_split (fun up => bodyProd τ p up) (fun uq => bodyProd τ q uq)
        (fun up => if up (Sum.inl ()) = true then 1 else 0)
        (fun uq => if uq (Sum.inl ()) = false then 1 else 0),
      sum_prod_split (fun up => bodyProd τ p up) (fun uq => bodyProd τ q uq)
        (fun up => if up (Sum.inl ()) = false then 1 else 0)
        (fun uq => if uq (Sum.inl ()) = true then 1 else 0),
      sum_pinned τ p true _ (fun _ => rfl), sum_pinned τ q false _ (fun _ => rfl),
      sum_pinned τ p false _ (fun _ => rfl), sum_pinned τ q true _ (fun _ => rfl)]
    simp

/-- **(SEM).**  The conditioned partition function of every subtree is `1` when its root is
inactive and the polynomial computed by the subtree when its root is active.  This is an
identity of polynomials in the original formula variables. -/
theorem condZ_spec {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    ∀ f : Formula ι F, condZ τ f false = 1 ∧ condZ τ f true = f.eval := by
  have h2 : (2 : MvPolynomial ι F) = 0 := two_eq_zero_of_algebra F
  intro f
  induction f with
  | var i =>
      refine ⟨?_, ?_⟩
      · rw [condZ_var hτ0 hτ1]; simp [boolVal]
      · rw [condZ_var hτ0 hτ1]
        show 1 + (1 + X i) * 1 = X i
        linear_combination h2
  | const c =>
      refine ⟨?_, ?_⟩
      · rw [condZ_const hτ0 hτ1]; simp [boolVal]
      · rw [condZ_const hτ0 hτ1]
        show 1 + (1 + C c) * 1 = C c
        linear_combination h2
  | add p q ihp ihq =>
      refine ⟨?_, ?_⟩
      · rw [condZ_add hτ0 hτ1]; simp [ihp.1, ihq.1]
      · rw [condZ_add hτ0 hτ1]
        simp only [if_neg (by simp : ¬ (true = false))]
        rw [ihp.1, ihp.2, ihq.1, ihq.2]
        show p.eval * 1 + 1 * q.eval = _
        rw [Formula.eval]
        ring
  | mul p q ihp ihq =>
      exact ⟨by rw [condZ_mul, ihp.1, ihq.1]; ring,
        by rw [condZ_mul, ihp.2, ihq.2]; rfl⟩

/-! ## The direct representation and its size -/

/-- **The direct representation.**  The root pin `z_root` followed by all body factors,
over the auxiliary cube `TAux f`. -/
noncomputable def directRep (τ : F) (f : Formula ι F) : AffineHypercubeRep ι F where
  aux := TAux f
  auxFintype := inferInstance
  auxDecEq := inferInstance
  factors := varForm (Sum.inr (Sum.inl ())) :: bodyFactors τ f

/-- **Direct compiler correctness.**  The direct representation computes the polynomial of
the formula, as an identity in the original variables. -/
theorem directRep_value (f : Formula ι F) {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (directRep τ f).value = f.eval := by
  have hval : (directRep τ f).value
      = ∑ u : TAux f → Bool, (boolVal (u (Sum.inl ())) : MvPolynomial ι F) * bodyProd τ f u := by
    refine Finset.sum_congr rfl fun u _ => ?_
    show ((varForm (Sum.inr (Sum.inl ())) :: bodyFactors τ f).map fun A =>
      A.eval ((directRep τ f).subst u)).prod = _
    rw [List.map_cons, List.prod_cons]
    congr 1
    simp [varForm, AffineForm.eval, AffineHypercubeRep.subst]
  rw [hval, sum_pinned τ f true _ fun u => by cases u (Sum.inl ()) <;> simp [boolVal]]
  exact (condZ_spec hτ0 hτ1 f).2

/-- The direct representation represents `f.eval`. -/
theorem directRep_represents (f : Formula ι F) {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (directRep τ f).Represents f.eval :=
  directRep_value f hτ0 hτ1

omit [CharP F 2] in
/-- **Support two.**  Every affine factor of the direct representation — the root pin, the
leaf gadgets, the branch gadgets and the multiplication relations — mentions at most two
variables. -/
theorem directRep_supportLE_two (τ : F) (f : Formula ι F) : (directRep τ f).SupportLE 2 := by
  intro A hA
  rcases List.mem_cons.mp hA with rfl | h
  · simp [varForm, numVars]
  · exact numVars_bodyFactors_le τ f A h

omit [CharP F 2] in
/-- **Exact auxiliary count** of the direct representation: `q = 2l + 2a + u`. -/
theorem directRep_numAux (τ : F) (f : Formula ι F) :
    (directRep τ f).numAux = 2 * f.leaves + 2 * f.addGates + f.mulGates :=
  card_taux f

omit [CharP F 2] in
/-- **Exact factor count** of the direct representation: `M = 1 + 3l + 6a + 2u`. -/
theorem directRep_numFactors (τ : F) (f : Formula ι F) :
    (directRep τ f).numFactors = 1 + (3 * f.leaves + 6 * f.addGates + 2 * f.mulGates) := by
  show (varForm (Sum.inr (Sum.inl ())) :: bodyFactors τ f).length = _
  rw [List.length_cons, length_bodyFactors]
  omega

omit [CharP F 2] in
/-- `q ≤ 2 s`. -/
theorem directRep_numAux_le (τ : F) (f : Formula ι F) :
    (directRep τ f).numAux ≤ 2 * f.size := by
  rw [directRep_numAux]
  have : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

omit [CharP F 2] in
/-- The sharp form `q = 2 s - u`, using the binary-tree identity `l = a + u + 1`. -/
theorem directRep_numAux_eq_two_size_sub (τ : F) (f : Formula ι F) :
    (directRep τ f).numAux = 2 * f.size - f.mulGates := by
  rw [directRep_numAux]
  have : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

omit [CharP F 2] in
/-- `2 M ≤ 9 s`. -/
theorem directRep_two_numFactors_le (τ : F) (f : Formula ι F) :
    2 * (directRep τ f).numFactors ≤ 9 * f.size := by
  rw [directRep_numFactors]
  have hl := leaves_eq_gates_succ f
  have : f.size = f.leaves + f.addGates + f.mulGates := rfl
  omega

omit [CharP F 2] in
/-- `M ≤ 5 s`. -/
theorem directRep_numFactors_le (τ : F) (f : Formula ι F) :
    (directRep τ f).numFactors ≤ 5 * f.size := by
  have h := directRep_two_numFactors_le τ f
  omega

/-- **The main finite direct compiler theorem.**

Over a field of characteristic two containing an element `τ ∉ {0, 1}`, every binary
division-free arithmetic formula `f` has an affine-product Boolean-hypercube representation

```
f(X) = ∑_{u : aux → Bool} ∏_j A_j(X, u)
```

with every affine factor of variable support at most **two**, at most `2 · size f` summed
Boolean auxiliaries and at most `5 · size f` affine factors (sharply, `2M ≤ 9 · size f`).
The proof goes through the direct formula-tree activation compiler; it does not use the
graph/path compiler. -/
theorem has_supportTwo_representation_direct (f : Formula ι F) {τ : F}
    (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    ∃ R : AffineHypercubeRep ι F,
      R.Represents f.eval ∧ R.SupportLE 2 ∧ R.numAux ≤ 2 * f.size ∧
        2 * R.numFactors ≤ 9 * f.size ∧ R.numFactors ≤ 5 * f.size :=
  ⟨directRep τ f, directRep_represents f hτ0 hτ1, directRep_supportLE_two τ f,
    directRep_numAux_le τ f, directRep_two_numFactors_le τ f, directRep_numFactors_le τ f⟩

/-- The direct compiler theorem under the canonical field hypothesis
`∃ τ : F, τ ≠ 0 ∧ τ ≠ 1`, which also covers infinite characteristic-two fields. -/
theorem has_supportTwo_representation_direct_of_exists_tau (f : Formula ι F)
    (hτ : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1) :
    ∃ R : AffineHypercubeRep ι F,
      R.Represents f.eval ∧ R.SupportLE 2 ∧ R.numAux ≤ 2 * f.size ∧
        2 * R.numFactors ≤ 9 * f.size ∧ R.numFactors ≤ 5 * f.size := by
  obtain ⟨τ, hτ0, hτ1⟩ := hτ
  exact f.has_supportTwo_representation_direct hτ0 hτ1

end Formula

end VNP1Char2
