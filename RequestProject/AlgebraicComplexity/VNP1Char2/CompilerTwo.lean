/-
# The generic support-two compiler

Input data:

* a finite type `A` of Boolean *selection* variables;
* a list `flowForms` of affine forms in the original variables and the selection variables,
  used **as they are** (they are affine already; for support two they must mention at most
  two variables);
* a finite type `T` of *ternary occurrences*, each carrying three selection variables
  `ta j, tb j, tc j` — these are the flow factors `1 + z_a + z_b + z_c` of a vertex of total
  degree three, which are affine but of support three and therefore have to be expanded;
* a finite type `K` of *quadratic occurrences*, each carrying two affine forms `x k`, `y k`,
  standing for a quadratic factor `1 + x_k y_k`.

Output: an `AffineHypercubeRep` with auxiliaries `A ⊕ (T ⊕ K)` — the selection bits
together with **one fresh auxiliary per gadget occurrence** — with

```
q = |A| + |T| + |K|,        M = #flowForms + 4|T| + 3|K|.
```

Two value theorems are proved.

* `compiled2_value_raw` is unconditional and keeps the cubic error of the ternary gadget
  visible;
* `compiled2_value` removes the error, under the hypothesis `hkill` that, **for each fixed
  Boolean selection `z`**, the error of each ternary occurrence annihilates the product of
  the quadratic factors.  This is the proof-order firewall of the memo: the error is killed
  pointwise on Boolean assignments, never by rewriting `a b c (1 + a b) = 0` inside an
  unrestricted polynomial ring.

Freshness of the auxiliaries is built into the index type `A ⊕ (T ⊕ K)`: distinct gadget
occurrences use distinct auxiliaries, and the flattening lemmas below are what justify
exchanging the products over `T` and `K` with the sums over their auxiliary cubes.  No
summed Boolean variable is introduced that does not occur in the body.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.Compiler
import RequestProject.AlgebraicComplexity.VNP1Char2.SupportTwoGadget

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace VNP1Char2

open scoped BigOperators
open AffineForm MvPolynomial

/-! ## Flattening a one-bit cube and a triple disjoint union -/

section Flatten

variable {M : Type*} [CommRing M]

/-- **Flattening, one auxiliary per occurrence.**  A product of one-bit gadget sums is a
single sum over the product cube of the products of the gadget bodies. -/
theorem prod_sum_flatten_one {J : Type*} [Fintype J] [DecidableEq J] (f : J → Bool → M) :
    (∏ j : J, ∑ h : Bool, f j h) = ∑ w : J → Bool, ∏ j : J, f j (w j) := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool)) (fun j h => f j h)]
  rw [Fintype.piFinset_univ]

/-- Flattening two independent gadget cubes sitting next to a common factor `c`. -/
theorem sum_cube_pair_flatten {T K : Type*} [Fintype T] [DecidableEq T]
    [Fintype K] [DecidableEq K] (c : M) (f : T → Bool → M) (g : K → Bool → M) :
    (∑ w : T → Bool, ∑ v : K → Bool, c * (∏ j : T, f j (w j)) * ∏ k : K, g k (v k))
      = c * (∏ j : T, ∑ h : Bool, f j h) * ∏ k : K, ∑ h : Bool, g k h := by
  calc (∑ w : T → Bool, ∑ v : K → Bool, c * (∏ j : T, f j (w j)) * ∏ k : K, g k (v k))
      = ∑ w : T → Bool, (c * ∏ j : T, f j (w j)) * ∑ v : K → Bool, ∏ k : K, g k (v k) :=
        Finset.sum_congr rfl fun w _ =>
          (Finset.mul_sum Finset.univ (fun v : K → Bool => ∏ k : K, g k (v k))
            (c * ∏ j : T, f j (w j))).symm
    _ = (∑ w : T → Bool, c * ∏ j : T, f j (w j)) * ∑ v : K → Bool, ∏ k : K, g k (v k) :=
        (Finset.sum_mul Finset.univ (fun w : T → Bool => c * ∏ j : T, f j (w j))
          (∑ v : K → Bool, ∏ k : K, g k (v k))).symm
    _ = (c * ∑ w : T → Bool, ∏ j : T, f j (w j)) * ∑ v : K → Bool, ∏ k : K, g k (v k) := by
        congr 1
        exact (Finset.mul_sum Finset.univ (fun w : T → Bool => ∏ j : T, f j (w j)) c).symm
    _ = c * (∏ j : T, ∑ h : Bool, f j h) * ∏ k : K, ∑ h : Bool, g k h := by
        rw [prod_sum_flatten_one f, prod_sum_flatten_one g]

/-- The Boolean cube on a triple disjoint union splits as a product of three cubes. -/
def cube3Equiv (A T K : Type*) :
    ((A ⊕ (T ⊕ K)) → Bool) ≃ (A → Bool) × ((T → Bool) × (K → Bool)) where
  toFun u := (fun a => u (Sum.inl a),
    (fun j => u (Sum.inr (Sum.inl j)), fun k => u (Sum.inr (Sum.inr k))))
  invFun p := Sum.elim p.1 (Sum.elim p.2.1 p.2.2)
  left_inv u := by
    funext c
    rcases c with a | (j | k) <;> rfl
  right_inv p := by
    obtain ⟨z, w, v⟩ := p
    rfl

/-- Merging the three cubes into one. -/
theorem sum_cube3 {A T K : Type*} [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]
    [Fintype K] [DecidableEq K] (g : (A → Bool) → (T → Bool) → (K → Bool) → M) :
    (∑ u : (A ⊕ (T ⊕ K)) → Bool, g (fun a => u (Sum.inl a)) (fun j => u (Sum.inr (Sum.inl j)))
        fun k => u (Sum.inr (Sum.inr k)))
      = ∑ z : A → Bool, ∑ w : T → Bool, ∑ v : K → Bool, g z w v := by
  have h1 : (∑ z : A → Bool, ∑ w : T → Bool, ∑ v : K → Bool, g z w v)
      = ∑ p : (A → Bool) × ((T → Bool) × (K → Bool)), g p.1 p.2.1 p.2.2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun z _ => by rw [Fintype.sum_prod_type]
  rw [h1]
  exact Fintype.sum_equiv (cube3Equiv A T K) _ _ fun u => rfl

/-- **Killing a pointwise-vanishing error inside a product.**  If every error term `e j`
annihilates `W`, then the errors may be dropped from the product. -/
theorem prod_add_err_mul {J : Type*} [Fintype J] [DecidableEq J] (p e : J → M) (W : M)
    (h : ∀ j, e j * W = 0) : (∏ j : J, (p j + e j)) * W = (∏ j : J, p j) * W := by
  have key : ∀ s : Finset J, (∏ j ∈ s, (p j + e j)) * W = (∏ j ∈ s, p j) * W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
        rw [Finset.prod_insert hj, Finset.prod_insert hj]
        have hsplit : (p j + e j) * (∏ i ∈ s, (p i + e i)) * W
            = p j * ((∏ i ∈ s, (p i + e i)) * W) + (∏ i ∈ s, (p i + e i)) * (e j * W) := by
          ring
        rw [hsplit, h j, mul_zero, add_zero, ih, mul_assoc]
  exact key Finset.univ

end Flatten

/-! ## The compiler -/

variable {ι A T K : Type} [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]
  [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [CharP F 2]

/-- The inclusion of the selection-variable index type into the full auxiliary index type
of the support-two compiler. -/
def embSel2 : (ι ⊕ A) → (ι ⊕ (A ⊕ (T ⊕ K))) := Sum.map id Sum.inl

/-- The index of the auxiliary of the `j`-th ternary occurrence. -/
def ternAux (j : T) : ι ⊕ (A ⊕ (T ⊕ K)) := Sum.inr (Sum.inr (Sum.inl j))

/-- The index of the auxiliary of the `k`-th quadratic occurrence. -/
def quadAux (k : K) : ι ⊕ (A ⊕ (T ⊕ K)) := Sum.inr (Sum.inr (Sum.inr k))

/-- The index of a selection variable inside the full auxiliary index type. -/
def selVar (a : A) : ι ⊕ (A ⊕ (T ⊕ K)) := Sum.inr (Sum.inl a)

/-- **The support-two compiled representation**: the flow factors, then four affine factors
for each ternary occurrence, then three affine factors for each quadratic occurrence. -/
noncomputable def compiled2 (τ : F) (flowForms : List (AffineForm (ι ⊕ A) F))
    (ta tb tc : T → A) (x y : K → AffineForm (ι ⊕ A) F) : AffineHypercubeRep ι F where
  aux := A ⊕ (T ⊕ K)
  auxFintype := inferInstance
  auxDecEq := inferInstance
  factors := flowForms.map (mapVar embSel2) ++
    ((Finset.univ : Finset T).toList.flatMap fun j =>
      ternFactors τ (selVar (ι := ι) (T := T) (K := K) (ta j)) (selVar (tb j)) (selVar (tc j))
        (ternAux (ι := ι) (A := A) (K := K) j)) ++
    ((Finset.univ : Finset K).toList.flatMap fun k =>
      gadget2Factors τ (mapVar embSel2 (x k)) (mapVar embSel2 (y k))
        (quadAux (ι := ι) (A := A) (T := T) k))

namespace compiled2

variable (τ : F) (flowForms : List (AffineForm (ι ⊕ A) F)) (ta tb tc : T → A)
  (x y : K → AffineForm (ι ⊕ A) F)

omit [CharP F 2] in
theorem factors_eq : (compiled2 τ flowForms ta tb tc x y).factors =
    flowForms.map (mapVar embSel2) ++
    ((Finset.univ : Finset T).toList.flatMap fun j =>
      ternFactors τ (selVar (ι := ι) (T := T) (K := K) (ta j)) (selVar (tb j)) (selVar (tc j))
        (ternAux (ι := ι) (A := A) (K := K) j)) ++
    ((Finset.univ : Finset K).toList.flatMap fun k =>
      gadget2Factors τ (mapVar embSel2 (x k)) (mapVar embSel2 (y k))
        (quadAux (ι := ι) (A := A) (T := T) k)) := rfl

omit [CharP F 2] in
/-- **Size accounting, auxiliaries**: `q = |A| + |T| + |K|`, one fresh bit per gadget. -/
theorem numAux_eq :
    (compiled2 τ flowForms ta tb tc x y).numAux
      = Fintype.card A + Fintype.card T + Fintype.card K := by
  show Fintype.card (A ⊕ (T ⊕ K)) = _
  simp [Fintype.card_sum, add_assoc]

omit [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T] [Fintype K] [DecidableEq K]
  [Field F] [CharP F 2] in
theorem length_flatMap_const {J : Type*} (c : ℕ) (g : J → List (AffineForm (ι ⊕ (A ⊕ (T ⊕ K))) F))
    (hg : ∀ j, (g j).length = c) (l : List J) : (l.flatMap g).length = c * l.length := by
  induction l with
  | nil => simp
  | cons j l ih => rw [List.flatMap_cons, List.length_append, ih, hg j, List.length_cons]; ring

omit [CharP F 2] in
/-- **Size accounting, factors**: `M = #flowForms + 4|T| + 3|K|`. -/
theorem numFactors_eq :
    (compiled2 τ flowForms ta tb tc x y).numFactors
      = flowForms.length + 4 * Fintype.card T + 3 * Fintype.card K := by
  show (List.length _) = _
  rw [factors_eq, List.length_append, List.length_append, List.length_map,
    length_flatMap_const 4 _ (fun j => length_ternFactors ..),
    length_flatMap_const 3 _ (fun k => length_gadget2Factors ..),
    Finset.length_toList, Finset.length_toList, Finset.card_univ, Finset.card_univ]

omit [CharP F 2] in
/-- **Support two.**  If every flow factor mentions at most two variables and the quadratic
gadget inputs are single variables (or constants), every factor of the compiled
representation mentions at most two variables. -/
theorem supportLE_two
    (hflow : ∀ Af ∈ flowForms, Af.numVars ≤ 2)
    (hx : ∀ k, (x k).numVars ≤ 1) (hy : ∀ k, (y k).numVars ≤ 1) :
    (compiled2 τ flowForms ta tb tc x y).SupportLE 2 := by
  intro Af hAf
  rw [factors_eq, List.mem_append, List.mem_append] at hAf
  rcases hAf with (h | h) | h
  · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp h
    rw [mapVar, numVars]
    simpa [numVars] using hflow B hB
  · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp h
    exact numVars_ternFactors_le hj
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
    have hbound := numVars_gadget2Factors_le hk
    have hx' : (mapVar (F := F) (embSel2 (ι := ι) (T := T) (K := K)) (x k)).numVars ≤ 1 := by
      simpa [mapVar, numVars] using hx k
    have hy' : (mapVar (F := F) (embSel2 (ι := ι) (T := T) (K := K)) (y k)).numVars ≤ 1 := by
      simpa [mapVar, numVars] using hy k
    omega

end compiled2

/-! ## The value of the compiled representation -/

section Value

variable (τ : F) (flowForms : List (AffineForm (ι ⊕ A) F)) (ta tb tc : T → A)
  (x y : K → AffineForm (ι ⊕ A) F)

omit [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T] [Fintype K] [DecidableEq K]
  [CharP F 2] in
theorem subst_comp_embSel2 (u : (A ⊕ (T ⊕ K)) → Bool) :
    (Sum.elim X fun a => boolVal (u a)) ∘ (embSel2 (ι := ι) (A := A) (T := T) (K := K))
      = (substSel (F := F) fun a => u (Sum.inl a)) := by
  funext w
  rcases w with i | a <;> rfl

omit [CharP F 2] in
/-- The product of the compiled factors at a Boolean point of the full cube. -/
theorem prod_factors_eval2 (u : (A ⊕ (T ⊕ K)) → Bool) :
    ((compiled2 τ flowForms ta tb tc x y).factors.map fun Af =>
        Af.eval ((compiled2 τ flowForms ta tb tc x y).subst u)).prod
      = (flowForms.map fun Af => Af.eval (substSel fun a => u (Sum.inl a))).prod
        * (∏ j : T, ternGadgetBody τ (boolVal (u (Sum.inl (ta j))) : MvPolynomial ι F)
            (boolVal (u (Sum.inl (tb j)))) (boolVal (u (Sum.inl (tc j))))
            (boolVal (u (Sum.inr (Sum.inl j)))))
        * ∏ k : K, twoGadgetBody τ ((x k).eval (substSel fun a => u (Sum.inl a)))
            ((y k).eval (substSel fun a => u (Sum.inl a)))
            (boolVal (u (Sum.inr (Sum.inr k)))) := by
  have hsubst : (compiled2 τ flowForms ta tb tc x y).subst u
      = Sum.elim X fun a => boolVal (u a) := rfl
  rw [compiled2.factors_eq]
  simp only [List.map_append, List.prod_append, List.map_map, Function.comp_def]
  congr 1
  · congr 1
    · refine congrArg List.prod (List.map_congr_left fun B _ => ?_)
      rw [hsubst, eval_mapVar, subst_comp_embSel2]
    · rw [List.map_flatMap]
      have hflat : ∀ l : List T, ((l.flatMap fun j =>
          (ternFactors τ (selVar (ι := ι) (T := T) (K := K) (ta j)) (selVar (tb j))
            (selVar (tc j)) (ternAux (ι := ι) (A := A) (K := K) j)).map fun Af =>
              Af.eval ((compiled2 τ flowForms ta tb tc x y).subst u))).prod
          = (l.map fun j => ternGadgetBody τ (boolVal (u (Sum.inl (ta j))) : MvPolynomial ι F)
              (boolVal (u (Sum.inl (tb j)))) (boolVal (u (Sum.inl (tc j))))
              (boolVal (u (Sum.inr (Sum.inl j))))).prod := by
        intro l
        induction l with
        | nil => simp
        | cons j l ih =>
            rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]
            congr 1
            rw [prod_ternFactors τ _ _ _ _ _ (u (Sum.inr (Sum.inl j))) (by rw [hsubst]; rfl)]
            rw [hsubst]
            rfl
      rw [← Finset.prod_map_toList]
      exact hflat _
  · rw [List.map_flatMap]
    have hflat : ∀ l : List K, ((l.flatMap fun k =>
        (gadget2Factors τ (mapVar embSel2 (x k)) (mapVar embSel2 (y k))
          (quadAux (ι := ι) (A := A) (T := T) k)).map fun Af =>
            Af.eval ((compiled2 τ flowForms ta tb tc x y).subst u))).prod
        = (l.map fun k => twoGadgetBody τ ((x k).eval (substSel fun a => u (Sum.inl a)))
            ((y k).eval (substSel fun a => u (Sum.inl a)))
            (boolVal (u (Sum.inr (Sum.inr k))))).prod := by
      intro l
      induction l with
      | nil => simp
      | cons k l ih =>
          rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]
          congr 1
          rw [prod_gadget2Factors τ _ _ _ _ (u (Sum.inr (Sum.inr k))) (by rw [hsubst]; rfl)]
          rw [hsubst, eval_mapVar, eval_mapVar, subst_comp_embSel2]
    rw [← Finset.prod_map_toList]
    exact hflat _

/-- **The raw compiler identity.**  The compiled representation computes the hypercube sum,
over the selection bits only, of the product of the flow factors, of the *ternary bodies
including their cubic errors*, and of the quadratic factors `1 + x_k y_k`. -/
theorem compiled2_value_raw (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (compiled2 τ flowForms ta tb tc x y).value
      = ∑ z : A → Bool, (flowForms.map fun Af => Af.eval (substSel z)).prod
          * (∏ j : T, ((1 + (boolVal (z (ta j)) : MvPolynomial ι F) + boolVal (z (tb j))
              + boolVal (z (tc j)))
              + algebraMap F (MvPolynomial ι F) (kappaVal τ)⁻¹ *
                  (boolVal (z (ta j)) * boolVal (z (tb j)) * boolVal (z (tc j)))))
          * ∏ k : K, (1 + (x k).eval (substSel z) * (y k).eval (substSel z)) := by
  show (∑ u : (A ⊕ (T ⊕ K)) → Bool,
      ((compiled2 τ flowForms ta tb tc x y).factors.map fun Af =>
        Af.eval ((compiled2 τ flowForms ta tb tc x y).subst u)).prod) = _
  rw [Finset.sum_congr rfl fun u _ => prod_factors_eval2 τ flowForms ta tb tc x y u]
  rw [sum_cube3 (M := MvPolynomial ι F)
      (g := fun (z : A → Bool) (w : T → Bool) (v : K → Bool) =>
        (flowForms.map fun Af => Af.eval (substSel (ι := ι) (F := F) z)).prod
          * (∏ j : T, ternGadgetBody τ (boolVal (z (ta j)) : MvPolynomial ι F)
              (boolVal (z (tb j))) (boolVal (z (tc j))) (boolVal (w j)))
          * ∏ k : K, twoGadgetBody τ ((x k).eval (substSel (ι := ι) (F := F) z))
              ((y k).eval (substSel (ι := ι) (F := F) z)) (boolVal (v k)))]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sum_cube_pair_flatten (flowForms.map fun Af =>
      Af.eval (substSel (ι := ι) (F := F) z)).prod
    (fun j h => ternGadgetBody τ (boolVal (z (ta j)) : MvPolynomial ι F) (boolVal (z (tb j)))
      (boolVal (z (tc j))) (boolVal h))
    (fun k h => twoGadgetBody τ ((x k).eval (substSel (ι := ι) (F := F) z))
      ((y k).eval (substSel (ι := ι) (F := F) z)) (boolVal h))]
  congr 1
  · congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    exact ternFactor_identity hτ0 hτ1 _ _ _
  · exact Finset.prod_congr rfl fun k _ => twoFactor_identity hτ0 hτ1 _ _

/-- **The support-two compiler identity.**  Under the *pointwise* hypothesis `hkill` — for
each fixed Boolean selection `z`, the cubic error of every ternary occurrence annihilates
the product of the quadratic factors — the compiled representation computes the hypercube
sum, over the selection bits only, of the product of the flow factors, of the affine
ternary flow factors `1 + z_a + z_b + z_c`, and of the quadratic factors `1 + x_k y_k`. -/
theorem compiled2_value (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)
    (hkill : ∀ (z : A → Bool) (j : T),
      (algebraMap F (MvPolynomial ι F) (kappaVal τ)⁻¹ *
          ((boolVal (z (ta j)) : MvPolynomial ι F) * boolVal (z (tb j)) * boolVal (z (tc j))))
        * (∏ k : K, (1 + (x k).eval (substSel z) * (y k).eval (substSel z))) = 0) :
    (compiled2 τ flowForms ta tb tc x y).value
      = ∑ z : A → Bool, (flowForms.map fun Af => Af.eval (substSel z)).prod
          * (∏ j : T, (1 + (boolVal (z (ta j)) : MvPolynomial ι F) + boolVal (z (tb j))
              + boolVal (z (tc j))))
          * ∏ k : K, (1 + (x k).eval (substSel z) * (y k).eval (substSel z)) := by
  rw [compiled2_value_raw τ flowForms ta tb tc x y hτ0 hτ1]
  refine Finset.sum_congr rfl fun z _ => ?_
  set Flow := (flowForms.map fun Af => Af.eval (substSel (ι := ι) (F := F) z)).prod with hFlow
  set Quad := ∏ k : K, (1 + (x k).eval (substSel (ι := ι) (F := F) z)
    * (y k).eval (substSel (ι := ι) (F := F) z)) with hQuad
  set p : T → MvPolynomial ι F := fun j => 1 + (boolVal (z (ta j)) : MvPolynomial ι F)
    + boolVal (z (tb j)) + boolVal (z (tc j)) with hp
  set e : T → MvPolynomial ι F := fun j =>
    algebraMap F (MvPolynomial ι F) (kappaVal τ)⁻¹ *
      ((boolVal (z (ta j)) : MvPolynomial ι F) * boolVal (z (tb j)) * boolVal (z (tc j))) with he
  have hW : ∀ j : T, e j * (Flow * Quad) = 0 := by
    intro j
    have h0 : e j * Quad = 0 := hkill z j
    calc e j * (Flow * Quad) = Flow * (e j * Quad) := by ring
      _ = 0 := by rw [h0, mul_zero]
  have hkey := prod_add_err_mul p e (Flow * Quad) hW
  calc Flow * (∏ j : T, (p j + e j)) * Quad = (∏ j : T, (p j + e j)) * (Flow * Quad) := by ring
    _ = (∏ j : T, p j) * (Flow * Quad) := hkey
    _ = Flow * (∏ j : T, p j) * Quad := by ring

end Value

end VNP1Char2
