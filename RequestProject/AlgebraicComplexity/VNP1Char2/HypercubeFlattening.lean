/-
# Flattening nested Boolean-hypercube sums

Two things are needed to turn a product of gadget expansions into a single hypercube sum
of a single product:

* `prod_sum_flatten`: a product over `k` of sums over the two auxiliaries of the `k`-th
  gadget equals one sum over *all* auxiliaries of the product.  Each gadget occurrence
  gets its own pair of auxiliaries; this is exactly the freshness requirement.
* `sumCubeEquiv`: the Boolean cube on a disjoint union of index sets is the product of the
  Boolean cubes, so the edge-selection bits and the gadget bits can be merged into a single
  cube.

The file also records two firewall examples:

* the false step `(∑_b A b) * (∑_c B c) = ∑_b A b * B b` (identifying the auxiliaries of
  two different gadgets) is refuted by an explicit counterexample;
* in characteristic two a summed Boolean variable that does not occur in the body destroys
  the value: `∑_{b ∈ {0,1}} 1 = 0`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.AffineForm

namespace VNP1Char2

open scoped BigOperators

variable {M : Type*} [CommRing M]

/-- **Flattening.**  A product of two-auxiliary gadget sums is a single sum over the
product cube of the products of the gadget bodies. -/
theorem prod_sum_flatten {K : Type*} [Fintype K] [DecidableEq K] (f : K → Bool → Bool → M) :
    (∏ k : K, ∑ b : Bool, ∑ e : Bool, f k b e)
      = ∑ w : K → Bool × Bool, ∏ k : K, f k (w k).1 (w k).2 := by
  have h1 : ∀ k : K, (∑ b : Bool, ∑ e : Bool, f k b e)
      = ∑ p : Bool × Bool, f k p.1 p.2 := fun k =>
    (Fintype.sum_prod_type (f := fun p : Bool × Bool => f k p.1 p.2)).symm
  simp_rw [h1]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Bool × Bool)))
    (fun k p => f k p.1 p.2)]
  rw [Fintype.piFinset_univ]

/-- The Boolean cube on a disjoint union splits as a product of Boolean cubes; here the
second factor is presented as a pair of bits per index. -/
def sumCubeEquiv (A K : Type*) : ((A ⊕ K × Bool) → Bool) ≃ (A → Bool) × (K → Bool × Bool) where
  toFun u := (fun a => u (Sum.inl a), fun k => (u (Sum.inr (k, false)), u (Sum.inr (k, true))))
  invFun p := Sum.elim p.1 fun q => if q.2 then (p.2 q.1).2 else (p.2 q.1).1
  left_inv u := by
    funext x
    rcases x with a | ⟨k, b⟩
    · rfl
    · cases b <;> rfl
  right_inv p := by
    obtain ⟨z, w⟩ := p
    simp only [Prod.mk.injEq]
    exact ⟨rfl, funext fun k => rfl⟩

/-- Merging the two cubes into one. -/
theorem sum_sumCube {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    (g : (A → Bool) → (K → Bool × Bool) → M) :
    (∑ u : (A ⊕ K × Bool) → Bool, g (fun a => u (Sum.inl a))
        (fun k => (u (Sum.inr (k, false)), u (Sum.inr (k, true)))))
      = ∑ z : A → Bool, ∑ w : K → Bool × Bool, g z w := by
  rw [Fintype.sum_prod_type (f := fun p : (A → Bool) × (K → Bool × Bool) => g p.1 p.2) |>.symm]
  exact Fintype.sum_equiv (sumCubeEquiv A K) _ _ fun u => rfl

/-! ### Firewall examples -/

/-- **The false step.**  Identifying the auxiliary bits of two different gadgets changes
the value: `(∑_b A b) * (∑_c B c) ≠ ∑_b A b * B b` in general. -/
example :
    (∑ b : Bool, (if b then 0 else 1 : ZMod 2)) * (∑ c : Bool, (if c then 1 else 0 : ZMod 2))
      ≠ ∑ b : Bool, (if b then 0 else 1 : ZMod 2) * (if b then 1 else 0 : ZMod 2) := by
  decide

/-- **Unused summed auxiliaries are forbidden**: in characteristic two, summing a body
that does not involve the auxiliary annihilates it. -/
theorem sum_bool_const (h2 : (2 : M) = 0) (x : M) : (∑ _b : Bool, x) = 0 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, two_smul]
  linear_combination x * h2

end VNP1Char2
