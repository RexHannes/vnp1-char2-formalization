/-
# From a binary division-free arithmetic formula to a bounded-degree labelled DAG

A formula is compiled into a labelled DAG in the standard series–parallel way:

* a leaf (variable or constant) becomes a single labelled edge;
* an addition takes the two child graphs, adds a fresh source, a fresh sink and four
  connector edges labelled `1`;
* a multiplication joins the left child's sink to the right child's source by a single
  connector edge labelled `1` (the two vertices are *not* identified: identifying them
  would break the degree invariant).

Every graph produced this way satisfies

* `indeg v + outdeg v ≤ 3` at every vertex,
* `indeg s = 0`, `outdeg t = 0`, `outdeg s ≤ 2`, `indeg t ≤ 2`,
* every edge label is a single variable or a constant,

and computes the polynomial of the formula.  Acyclicity is built in: every graph carries a
rank function strictly increasing along edges, together with a depth bound used to shift
ranks when graphs are composed.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.SupportThree

namespace VNP1Char2

open scoped BigOperators
open AffineForm MvPolynomial

/-- A finite labelled DAG bundled with its finiteness instances and a depth bound for the
rank function. -/
structure LabelledDag (ι F : Type) where
  /-- vertices -/
  V : Type
  /-- edges -/
  E : Type
  /-- vertices form a finite type -/
  fV : Fintype V
  /-- vertex equality is decidable -/
  dV : DecidableEq V
  /-- edges form a finite type -/
  fE : Fintype E
  /-- edge equality is decidable -/
  dE : DecidableEq E
  /-- the underlying graph -/
  G : PathGraph V E
  /-- the affine edge labels -/
  lab : E → AffineForm ι F
  /-- a strict upper bound for the rank function -/
  depth : ℕ
  /-- the rank function is bounded by `depth` -/
  rank_lt_depth : ∀ v, G.rank v < depth

attribute [instance] LabelledDag.fV LabelledDag.dV LabelledDag.fE LabelledDag.dE

namespace LabelledDag

variable {ι F : Type} [Field F]

/-- The polynomial labels of the edges. -/
noncomputable def polyLab (D : LabelledDag ι F) : D.E → MvPolynomial ι F :=
  fun a => (D.lab a).eval (X : ι → MvPolynomial ι F)

/-- The polynomial computed by the DAG. -/
noncomputable def value (D : LabelledDag ι F) : MvPolynomial ι F :=
  PathGraph.val D.G D.polyLab

end LabelledDag

/-! ## The three constructors -/

variable {ι F : Type} [Field F]

/-- A single labelled edge from a fresh source to a fresh sink. -/
def leafDag (A : AffineForm ι F) : LabelledDag ι F where
  V := Bool
  E := Unit
  fV := inferInstance
  dV := inferInstance
  fE := inferInstance
  dE := inferInstance
  G :=
    { src := fun _ => false
      tgt := fun _ => true
      s := false
      t := true
      hst := by decide
      rank := fun b => if b then 1 else 0
      rank_lt := by intro _; simp }
  lab := fun _ => A
  depth := 2
  rank_lt_depth := by intro v; cases v <;> simp

/-- The connector edges of an addition: `(false, b)` goes from the fresh source to the
source of child `b`, and `(true, b)` goes from the sink of child `b` to the fresh sink. -/
abbrev AddConn : Type := Bool × Bool

/-- Addition: fresh source, fresh sink and four connector edges labelled `1`. -/
def addDag (P Q : LabelledDag ι F) : LabelledDag ι F where
  V := (P.V ⊕ Q.V) ⊕ Bool
  E := (P.E ⊕ Q.E) ⊕ AddConn
  fV := inferInstance
  dV := inferInstance
  fE := inferInstance
  dE := inferInstance
  G :=
    { src := fun e => match e with
        | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl (P.G.src a))
        | Sum.inl (Sum.inr a) => Sum.inl (Sum.inr (Q.G.src a))
        | Sum.inr (false, _) => Sum.inr false
        | Sum.inr (true, false) => Sum.inl (Sum.inl P.G.t)
        | Sum.inr (true, true) => Sum.inl (Sum.inr Q.G.t)
      tgt := fun e => match e with
        | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl (P.G.tgt a))
        | Sum.inl (Sum.inr a) => Sum.inl (Sum.inr (Q.G.tgt a))
        | Sum.inr (false, false) => Sum.inl (Sum.inl P.G.s)
        | Sum.inr (false, true) => Sum.inl (Sum.inr Q.G.s)
        | Sum.inr (true, _) => Sum.inr true
      s := Sum.inr false
      t := Sum.inr true
      hst := by simp
      rank := fun v => match v with
        | Sum.inl (Sum.inl w) => 1 + P.G.rank w
        | Sum.inl (Sum.inr w) => 1 + Q.G.rank w
        | Sum.inr false => 0
        | Sum.inr true => 1 + max P.depth Q.depth
      rank_lt := by
        rintro ((a | a) | ⟨b, c⟩)
        · simpa using P.G.rank_lt a
        · simpa using Q.G.rank_lt a
        · cases b <;> cases c <;> simp
          · have := P.rank_lt_depth P.G.t
            have : P.depth ≤ max P.depth Q.depth := le_max_left _ _
            omega
          · have := Q.rank_lt_depth Q.G.t
            have : Q.depth ≤ max P.depth Q.depth := le_max_right _ _
            omega }
  lab := fun e => match e with
    | Sum.inl (Sum.inl a) => P.lab a
    | Sum.inl (Sum.inr a) => Q.lab a
    | Sum.inr _ => ⟨1, []⟩
  depth := 2 + max P.depth Q.depth
  rank_lt_depth := by
    rintro ((w | w) | b)
    · have := P.rank_lt_depth w
      have : P.depth ≤ max P.depth Q.depth := le_max_left _ _
      simp only []
      omega
    · have := Q.rank_lt_depth w
      have : Q.depth ≤ max P.depth Q.depth := le_max_right _ _
      simp only []
      omega
    · cases b <;> simp <;> omega

/-- Multiplication: one connector edge labelled `1` from the left sink to the right
source. -/
def mulDag (P Q : LabelledDag ι F) : LabelledDag ι F where
  V := P.V ⊕ Q.V
  E := (P.E ⊕ Q.E) ⊕ Unit
  fV := inferInstance
  dV := inferInstance
  fE := inferInstance
  dE := inferInstance
  G :=
    { src := fun e => match e with
        | Sum.inl (Sum.inl a) => Sum.inl (P.G.src a)
        | Sum.inl (Sum.inr a) => Sum.inr (Q.G.src a)
        | Sum.inr _ => Sum.inl P.G.t
      tgt := fun e => match e with
        | Sum.inl (Sum.inl a) => Sum.inl (P.G.tgt a)
        | Sum.inl (Sum.inr a) => Sum.inr (Q.G.tgt a)
        | Sum.inr _ => Sum.inr Q.G.s
      s := Sum.inl P.G.s
      t := Sum.inr Q.G.t
      hst := by simp
      rank := fun v => match v with
        | Sum.inl w => P.G.rank w
        | Sum.inr w => P.depth + Q.G.rank w
      rank_lt := by
        rintro ((a | a) | u)
        · simpa using P.G.rank_lt a
        · simpa using Q.G.rank_lt a
        · have := P.rank_lt_depth P.G.t
          simp only []
          omega }
  lab := fun e => match e with
    | Sum.inl (Sum.inl a) => P.lab a
    | Sum.inl (Sum.inr a) => Q.lab a
    | Sum.inr _ => ⟨1, []⟩
  depth := P.depth + Q.depth
  rank_lt_depth := by
    rintro (w | w)
    · have := P.rank_lt_depth w
      have := Q.rank_lt_depth Q.G.s
      simp only []
      omega
    · have := Q.rank_lt_depth w
      simp only []
      omega

/-! ## Structural simp lemmas -/

namespace PathGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {M : Type*} [CommRing M]

/-- The dynamic program, with the sum written over the whole edge type. -/
theorem valTo_eq_sum_univ (G : PathGraph V E) (l : E → M) (v : V) :
    G.valTo l v = (if v = G.s then 1 else 0)
      + ∑ a : E, (if G.tgt a = v then l a * G.valTo l (G.src a) else 0) := by
  rw [valTo_eq, inEdges, Finset.sum_filter]

end PathGraph

namespace LabelledDag

variable (P Q : LabelledDag ι F)

@[simp] theorem mulDag_s : (mulDag P Q).G.s = Sum.inl P.G.s := rfl
@[simp] theorem mulDag_t : (mulDag P Q).G.t = Sum.inr Q.G.t := rfl
@[simp] theorem mulDag_src_inl_inl (a : P.E) :
    (mulDag P Q).G.src (Sum.inl (Sum.inl a)) = Sum.inl (P.G.src a) := rfl
@[simp] theorem mulDag_src_inl_inr (a : Q.E) :
    (mulDag P Q).G.src (Sum.inl (Sum.inr a)) = Sum.inr (Q.G.src a) := rfl
@[simp] theorem mulDag_src_inr (u : Unit) :
    (mulDag P Q).G.src (Sum.inr u) = Sum.inl P.G.t := rfl
@[simp] theorem mulDag_tgt_inl_inl (a : P.E) :
    (mulDag P Q).G.tgt (Sum.inl (Sum.inl a)) = Sum.inl (P.G.tgt a) := rfl
@[simp] theorem mulDag_tgt_inl_inr (a : Q.E) :
    (mulDag P Q).G.tgt (Sum.inl (Sum.inr a)) = Sum.inr (Q.G.tgt a) := rfl
@[simp] theorem mulDag_tgt_inr (u : Unit) :
    (mulDag P Q).G.tgt (Sum.inr u) = Sum.inr Q.G.s := rfl
@[simp] theorem mulDag_polyLab_inl_inl (a : P.E) :
    (mulDag P Q).polyLab (Sum.inl (Sum.inl a)) = P.polyLab a := rfl
@[simp] theorem mulDag_polyLab_inl_inr (a : Q.E) :
    (mulDag P Q).polyLab (Sum.inl (Sum.inr a)) = Q.polyLab a := rfl
@[simp] theorem mulDag_polyLab_inr (u : Unit) :
    (mulDag P Q).polyLab (Sum.inr u) = 1 := by
  show AffineForm.eval (⟨1, []⟩ : AffineForm ι F) _ = 1
  simp [AffineForm.eval]

@[simp] theorem addDag_s : (addDag P Q).G.s = Sum.inr false := rfl
@[simp] theorem addDag_t : (addDag P Q).G.t = Sum.inr true := rfl
@[simp] theorem addDag_src_inl_inl (a : P.E) :
    (addDag P Q).G.src (Sum.inl (Sum.inl a)) = Sum.inl (Sum.inl (P.G.src a)) := rfl
@[simp] theorem addDag_src_inl_inr (a : Q.E) :
    (addDag P Q).G.src (Sum.inl (Sum.inr a)) = Sum.inl (Sum.inr (Q.G.src a)) := rfl
@[simp] theorem addDag_src_inr_false (c : Bool) :
    (addDag P Q).G.src (Sum.inr (false, c)) = Sum.inr false := by cases c <;> rfl
@[simp] theorem addDag_src_inr_true_false :
    (addDag P Q).G.src (Sum.inr (true, false)) = Sum.inl (Sum.inl P.G.t) := rfl
@[simp] theorem addDag_src_inr_true_true :
    (addDag P Q).G.src (Sum.inr (true, true)) = Sum.inl (Sum.inr Q.G.t) := rfl
@[simp] theorem addDag_tgt_inl_inl (a : P.E) :
    (addDag P Q).G.tgt (Sum.inl (Sum.inl a)) = Sum.inl (Sum.inl (P.G.tgt a)) := rfl
@[simp] theorem addDag_tgt_inl_inr (a : Q.E) :
    (addDag P Q).G.tgt (Sum.inl (Sum.inr a)) = Sum.inl (Sum.inr (Q.G.tgt a)) := rfl
@[simp] theorem addDag_tgt_inr_false_false :
    (addDag P Q).G.tgt (Sum.inr (false, false)) = Sum.inl (Sum.inl P.G.s) := rfl
@[simp] theorem addDag_tgt_inr_false_true :
    (addDag P Q).G.tgt (Sum.inr (false, true)) = Sum.inl (Sum.inr Q.G.s) := rfl
@[simp] theorem addDag_tgt_inr_true (c : Bool) :
    (addDag P Q).G.tgt (Sum.inr (true, c)) = Sum.inr true := by cases c <;> rfl
@[simp] theorem addDag_polyLab_inl_inl (a : P.E) :
    (addDag P Q).polyLab (Sum.inl (Sum.inl a)) = P.polyLab a := rfl
@[simp] theorem addDag_polyLab_inl_inr (a : Q.E) :
    (addDag P Q).polyLab (Sum.inl (Sum.inr a)) = Q.polyLab a := rfl
@[simp] theorem addDag_polyLab_inr (c : AddConn) :
    (addDag P Q).polyLab (Sum.inr c) = 1 := by
  show AffineForm.eval (⟨1, []⟩ : AffineForm ι F) _ = 1
  simp [AffineForm.eval]

@[simp] theorem mulDag_V_inl_inj (x y : P.V) :
    (@Eq (mulDag P Q).V (Sum.inl x) (Sum.inl y)) ↔ x = y :=
  ⟨fun h => Sum.inl_injective h, fun h => by rw [h]⟩

@[simp] theorem mulDag_V_inr_inj (x y : Q.V) :
    (@Eq (mulDag P Q).V (Sum.inr x) (Sum.inr y)) ↔ x = y :=
  ⟨fun h => Sum.inr_injective h, fun h => by rw [h]⟩

@[simp] theorem mulDag_V_inl_ne_inr (x : P.V) (y : Q.V) :
    (@Eq (mulDag P Q).V (Sum.inl x) (Sum.inr y)) ↔ False :=
  iff_false_intro fun h => by
    have h' : (Sum.inl x : P.V ⊕ Q.V) = Sum.inr y := h
    simp at h'

@[simp] theorem mulDag_V_inr_ne_inl (x : Q.V) (y : P.V) :
    (@Eq (mulDag P Q).V (Sum.inr x) (Sum.inl y)) ↔ False :=
  iff_false_intro fun h => by
    have h' : (Sum.inr x : P.V ⊕ Q.V) = Sum.inl y := h
    simp at h'

@[simp] theorem addDag_V_inll_inj (x y : P.V) :
    (@Eq (addDag P Q).V (Sum.inl (Sum.inl x)) (Sum.inl (Sum.inl y))) ↔ x = y :=
  ⟨fun h => Sum.inl_injective (Sum.inl_injective h), fun h => by rw [h]⟩

@[simp] theorem addDag_V_inlr_inj (x y : Q.V) :
    (@Eq (addDag P Q).V (Sum.inl (Sum.inr x)) (Sum.inl (Sum.inr y))) ↔ x = y :=
  ⟨fun h => Sum.inr_injective (Sum.inl_injective h), fun h => by rw [h]⟩

@[simp] theorem addDag_V_inll_ne_inlr (x : P.V) (y : Q.V) :
    (@Eq (addDag P Q).V (Sum.inl (Sum.inl x)) (Sum.inl (Sum.inr y))) ↔ False :=
  iff_false_intro fun h => by
    have h' : (Sum.inl (Sum.inl x) : (P.V ⊕ Q.V) ⊕ Bool) = Sum.inl (Sum.inr y) := h
    simp at h'

@[simp] theorem addDag_V_inlr_ne_inll (x : Q.V) (y : P.V) :
    (@Eq (addDag P Q).V (Sum.inl (Sum.inr x)) (Sum.inl (Sum.inl y))) ↔ False :=
  iff_false_intro fun h => by
    have h' : (Sum.inl (Sum.inr x) : (P.V ⊕ Q.V) ⊕ Bool) = Sum.inl (Sum.inl y) := h
    simp at h'

@[simp] theorem addDag_V_inl_ne_inr (x : P.V ⊕ Q.V) (b : Bool) :
    (@Eq (addDag P Q).V (Sum.inl x) (Sum.inr b)) ↔ False :=
  iff_false_intro fun h => by
    have h' : (Sum.inl x : (P.V ⊕ Q.V) ⊕ Bool) = Sum.inr b := h
    simp at h'

@[simp] theorem addDag_V_inr_ne_inl (b : Bool) (x : P.V ⊕ Q.V) :
    (@Eq (addDag P Q).V (Sum.inr b) (Sum.inl x)) ↔ False :=
  iff_false_intro fun h => by
    have h' : (Sum.inr b : (P.V ⊕ Q.V) ⊕ Bool) = Sum.inl x := h
    simp at h'

@[simp] theorem addDag_V_inr_inj (b c : Bool) :
    (@Eq (addDag P Q).V (Sum.inr b) (Sum.inr c)) ↔ b = c :=
  ⟨fun h => Sum.inr_injective h, fun h => by rw [h]⟩

/-- Splitting a sum over the edges of a product graph. -/
theorem mulDag_sum_edges {M : Type*} [AddCommMonoid M] (f : (mulDag P Q).E → M) :
    (∑ a, f a) = ((∑ a : P.E, f (Sum.inl (Sum.inl a))) + ∑ a : Q.E, f (Sum.inl (Sum.inr a)))
      + f (Sum.inr ()) := by
  show (∑ a : (P.E ⊕ Q.E) ⊕ Unit, f a) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

/-- Splitting a sum over the edges of a sum graph. -/
theorem addDag_sum_edges {M : Type*} [AddCommMonoid M] (f : (addDag P Q).E → M) :
    (∑ a, f a) = ((∑ a : P.E, f (Sum.inl (Sum.inl a))) + ∑ a : Q.E, f (Sum.inl (Sum.inr a)))
      + (f (Sum.inr (false, false)) + f (Sum.inr (false, true))
        + (f (Sum.inr (true, false)) + f (Sum.inr (true, true)))) := by
  show (∑ a : (P.E ⊕ Q.E) ⊕ AddConn, f a) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  abel

/-- Splitting a sum over the single edge of a leaf graph. -/
theorem leafDag_sum_edges {M : Type*} [AddCommMonoid M] (A : AffineForm ι F)
    (f : (leafDag A).E → M) : (∑ a, f a) = f () := by
  show (∑ _a : Unit, f ()) = _
  simp

/-! ## Value preservation -/

/-- Inside a product graph, the dynamic program on the left part is unchanged. -/
theorem mulDag_valTo_inl : ∀ (n : ℕ) (v : P.V), P.G.rank v = n →
    (mulDag P Q).G.valTo (mulDag P Q).polyLab (Sum.inl v) = P.G.valTo P.polyLab v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    have key : ∀ a : P.E,
        (if (mulDag P Q).G.tgt (Sum.inl (Sum.inl a)) = Sum.inl v then
            (mulDag P Q).polyLab (Sum.inl (Sum.inl a)) *
              (mulDag P Q).G.valTo (mulDag P Q).polyLab
                ((mulDag P Q).G.src (Sum.inl (Sum.inl a))) else 0)
          = (if P.G.tgt a = v then P.polyLab a * P.G.valTo P.polyLab (P.G.src a) else 0) := by
      intro a
      simp only [mulDag_tgt_inl_inl, mulDag_polyLab_inl_inl, mulDag_src_inl_inl, mulDag_V_inl_inj]
      by_cases h : P.G.tgt a = v
      · rw [if_pos h, if_pos h, ih (P.G.rank (P.G.src a)) (by have hlt := P.G.rank_lt a; rw [h, hv] at hlt; exact hlt) _ rfl]
      · rw [if_neg h, if_neg h]
    have hzeroQ : ∀ a : Q.E,
        (if (mulDag P Q).G.tgt (Sum.inl (Sum.inr a)) = Sum.inl v then
            (mulDag P Q).polyLab (Sum.inl (Sum.inr a)) *
              (mulDag P Q).G.valTo (mulDag P Q).polyLab
                ((mulDag P Q).G.src (Sum.inl (Sum.inr a))) else 0) = 0 := by
      intro a; simp
    have hconn : (if (mulDag P Q).G.tgt (Sum.inr ()) = Sum.inl v then
        (mulDag P Q).polyLab (Sum.inr ()) *
          (mulDag P Q).G.valTo (mulDag P Q).polyLab ((mulDag P Q).G.src (Sum.inr ()))
        else 0) = 0 := by simp
    rw [PathGraph.valTo_eq_sum_univ, PathGraph.valTo_eq_sum_univ P.G,
      mulDag_sum_edges (M := MvPolynomial ι F), Finset.sum_congr rfl (fun a _ => key a),
      Finset.sum_congr rfl (fun a _ => hzeroQ a), hconn]
    simp only [mulDag_s, mulDag_V_inl_inj, Finset.sum_const_zero, add_zero]

/-- Inside a product graph, the dynamic program on the right part is the left value times
the right dynamic program. -/
theorem mulDag_valTo_inr : ∀ (n : ℕ) (v : Q.V), Q.G.rank v = n →
    (mulDag P Q).G.valTo (mulDag P Q).polyLab (Sum.inr v)
      = P.value * Q.G.valTo Q.polyLab v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    have key : ∀ a : Q.E,
        (if (mulDag P Q).G.tgt (Sum.inl (Sum.inr a)) = Sum.inr v then
            (mulDag P Q).polyLab (Sum.inl (Sum.inr a)) *
              (mulDag P Q).G.valTo (mulDag P Q).polyLab
                ((mulDag P Q).G.src (Sum.inl (Sum.inr a))) else 0)
          = P.value *
              (if Q.G.tgt a = v then Q.polyLab a * Q.G.valTo Q.polyLab (Q.G.src a) else 0) := by
      intro a
      simp only [mulDag_tgt_inl_inr, mulDag_polyLab_inl_inr, mulDag_src_inl_inr, mulDag_V_inr_inj]
      by_cases h : Q.G.tgt a = v
      · rw [if_pos h, if_pos h, ih (Q.G.rank (Q.G.src a)) (by have hlt := Q.G.rank_lt a; rw [h, hv] at hlt; exact hlt) _ rfl]
        ring
      · rw [if_neg h, if_neg h, mul_zero]
    have hzeroP : ∀ a : P.E,
        (if (mulDag P Q).G.tgt (Sum.inl (Sum.inl a)) = Sum.inr v then
            (mulDag P Q).polyLab (Sum.inl (Sum.inl a)) *
              (mulDag P Q).G.valTo (mulDag P Q).polyLab
                ((mulDag P Q).G.src (Sum.inl (Sum.inl a))) else 0) = 0 := by
      intro a; simp
    have hconn : (if (mulDag P Q).G.tgt (Sum.inr ()) = Sum.inr v then
        (mulDag P Q).polyLab (Sum.inr ()) *
          (mulDag P Q).G.valTo (mulDag P Q).polyLab ((mulDag P Q).G.src (Sum.inr ()))
        else 0) = P.value * (if v = Q.G.s then 1 else 0) := by
      simp only [mulDag_tgt_inr, mulDag_polyLab_inr, mulDag_src_inr, mulDag_V_inr_inj, one_mul]
      rw [mulDag_valTo_inl P Q (P.G.rank P.G.t) _ rfl]
      by_cases h : Q.G.s = v
      · rw [if_pos h, if_pos h.symm, mul_one]; rfl
      · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
    rw [PathGraph.valTo_eq_sum_univ, PathGraph.valTo_eq_sum_univ Q.G,
      mulDag_sum_edges (M := MvPolynomial ι F), Finset.sum_congr rfl (fun a _ => key a),
      Finset.sum_congr rfl (fun a _ => hzeroP a), hconn, ← Finset.mul_sum]
    simp only [mulDag_s, mulDag_V_inr_ne_inl, if_false, Finset.sum_const_zero, zero_add]
    ring

/-- **Multiplication is computed correctly.** -/
theorem mulDag_value : (mulDag P Q).value = P.value * Q.value := by
  show (mulDag P Q).G.valTo _ (Sum.inr Q.G.t) = _
  rw [mulDag_valTo_inr P Q (Q.G.rank Q.G.t) _ rfl]
  rfl

/-- The fresh source of a sum graph carries the value `1`. -/
theorem addDag_valTo_src :
    (addDag P Q).G.valTo (addDag P Q).polyLab (Sum.inr false) = 1 := by
  have hP : ∀ a : P.E,
      (if (addDag P Q).G.tgt (Sum.inl (Sum.inl a)) = Sum.inr false then
          (addDag P Q).polyLab (Sum.inl (Sum.inl a)) *
            (addDag P Q).G.valTo (addDag P Q).polyLab
              ((addDag P Q).G.src (Sum.inl (Sum.inl a))) else 0) = 0 := by
    intro a; simp
  have hQ : ∀ a : Q.E,
      (if (addDag P Q).G.tgt (Sum.inl (Sum.inr a)) = Sum.inr false then
          (addDag P Q).polyLab (Sum.inl (Sum.inr a)) *
            (addDag P Q).G.valTo (addDag P Q).polyLab
              ((addDag P Q).G.src (Sum.inl (Sum.inr a))) else 0) = 0 := by
    intro a; simp
  have hc : ∀ c : AddConn,
      (if (addDag P Q).G.tgt (Sum.inr c) = Sum.inr false then
          (addDag P Q).polyLab (Sum.inr c) *
            (addDag P Q).G.valTo (addDag P Q).polyLab
              ((addDag P Q).G.src (Sum.inr c)) else 0) = 0 := by
    rintro ⟨b, c⟩
    cases b <;> cases c <;> simp
  rw [PathGraph.valTo_eq_sum_univ, addDag_sum_edges (M := MvPolynomial ι F),
    Finset.sum_congr rfl (fun a _ => hP a), Finset.sum_congr rfl (fun a _ => hQ a),
    hc (false, false), hc (false, true), hc (true, false), hc (true, true)]
  simp

/-- Inside a sum graph, the dynamic program on the left part is unchanged. -/
theorem addDag_valTo_inl_inl : ∀ (n : ℕ) (v : P.V), P.G.rank v = n →
    (addDag P Q).G.valTo (addDag P Q).polyLab (Sum.inl (Sum.inl v)) = P.G.valTo P.polyLab v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    have key : ∀ a : P.E,
        (if (addDag P Q).G.tgt (Sum.inl (Sum.inl a)) = Sum.inl (Sum.inl v) then
            (addDag P Q).polyLab (Sum.inl (Sum.inl a)) *
              (addDag P Q).G.valTo (addDag P Q).polyLab
                ((addDag P Q).G.src (Sum.inl (Sum.inl a))) else 0)
          = (if P.G.tgt a = v then P.polyLab a * P.G.valTo P.polyLab (P.G.src a) else 0) := by
      intro a
      simp only [addDag_tgt_inl_inl, addDag_polyLab_inl_inl, addDag_src_inl_inl,
        addDag_V_inll_inj]
      by_cases h : P.G.tgt a = v
      · rw [if_pos h, if_pos h, ih (P.G.rank (P.G.src a)) (by have hlt := P.G.rank_lt a; rw [h, hv] at hlt; exact hlt) _ rfl]
      · rw [if_neg h, if_neg h]
    have hzeroQ : ∀ a : Q.E,
        (if (addDag P Q).G.tgt (Sum.inl (Sum.inr a)) = Sum.inl (Sum.inl v) then
            (addDag P Q).polyLab (Sum.inl (Sum.inr a)) *
              (addDag P Q).G.valTo (addDag P Q).polyLab
                ((addDag P Q).G.src (Sum.inl (Sum.inr a))) else 0) = 0 := by
      intro a; simp
    have hc1 : (if (addDag P Q).G.tgt (Sum.inr (false, false)) = Sum.inl (Sum.inl v) then
        (addDag P Q).polyLab (Sum.inr (false, false)) *
          (addDag P Q).G.valTo (addDag P Q).polyLab
            ((addDag P Q).G.src (Sum.inr (false, false))) else 0)
        = (if v = P.G.s then 1 else 0) := by
      simp only [addDag_tgt_inr_false_false, addDag_polyLab_inr, addDag_src_inr_false,
        addDag_V_inll_inj, one_mul]
      rw [addDag_valTo_src P Q]
      by_cases h : P.G.s = v
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    have hc2 : (if (addDag P Q).G.tgt (Sum.inr (false, true)) = Sum.inl (Sum.inl v) then
        (addDag P Q).polyLab (Sum.inr (false, true)) *
          (addDag P Q).G.valTo (addDag P Q).polyLab
            ((addDag P Q).G.src (Sum.inr (false, true))) else 0) = 0 := by simp
    have hc3 : (if (addDag P Q).G.tgt (Sum.inr (true, false)) = Sum.inl (Sum.inl v) then
        (addDag P Q).polyLab (Sum.inr (true, false)) *
          (addDag P Q).G.valTo (addDag P Q).polyLab
            ((addDag P Q).G.src (Sum.inr (true, false))) else 0) = 0 := by simp
    have hc4 : (if (addDag P Q).G.tgt (Sum.inr (true, true)) = Sum.inl (Sum.inl v) then
        (addDag P Q).polyLab (Sum.inr (true, true)) *
          (addDag P Q).G.valTo (addDag P Q).polyLab
            ((addDag P Q).G.src (Sum.inr (true, true))) else 0) = 0 := by simp
    rw [PathGraph.valTo_eq_sum_univ, PathGraph.valTo_eq_sum_univ P.G,
      addDag_sum_edges (M := MvPolynomial ι F), Finset.sum_congr rfl (fun a _ => key a),
      Finset.sum_congr rfl (fun a _ => hzeroQ a), hc1, hc2, hc3, hc4]
    simp only [addDag_s, addDag_V_inl_ne_inr, if_false, Finset.sum_const_zero, zero_add,
      add_zero]
    ring

/-- Inside a sum graph, the dynamic program on the right part is unchanged. -/
theorem addDag_valTo_inl_inr : ∀ (n : ℕ) (v : Q.V), Q.G.rank v = n →
    (addDag P Q).G.valTo (addDag P Q).polyLab (Sum.inl (Sum.inr v)) = Q.G.valTo Q.polyLab v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    have key : ∀ a : Q.E,
        (if (addDag P Q).G.tgt (Sum.inl (Sum.inr a)) = Sum.inl (Sum.inr v) then
            (addDag P Q).polyLab (Sum.inl (Sum.inr a)) *
              (addDag P Q).G.valTo (addDag P Q).polyLab
                ((addDag P Q).G.src (Sum.inl (Sum.inr a))) else 0)
          = (if Q.G.tgt a = v then Q.polyLab a * Q.G.valTo Q.polyLab (Q.G.src a) else 0) := by
      intro a
      simp only [addDag_tgt_inl_inr, addDag_polyLab_inl_inr, addDag_src_inl_inr,
        addDag_V_inlr_inj]
      by_cases h : Q.G.tgt a = v
      · rw [if_pos h, if_pos h, ih (Q.G.rank (Q.G.src a)) (by have hlt := Q.G.rank_lt a; rw [h, hv] at hlt; exact hlt) _ rfl]
      · rw [if_neg h, if_neg h]
    have hzeroP : ∀ a : P.E,
        (if (addDag P Q).G.tgt (Sum.inl (Sum.inl a)) = Sum.inl (Sum.inr v) then
            (addDag P Q).polyLab (Sum.inl (Sum.inl a)) *
              (addDag P Q).G.valTo (addDag P Q).polyLab
                ((addDag P Q).G.src (Sum.inl (Sum.inl a))) else 0) = 0 := by
      intro a; simp
    have hc1 : (if (addDag P Q).G.tgt (Sum.inr (false, false)) = Sum.inl (Sum.inr v) then
        (addDag P Q).polyLab (Sum.inr (false, false)) *
          (addDag P Q).G.valTo (addDag P Q).polyLab
            ((addDag P Q).G.src (Sum.inr (false, false))) else 0) = 0 := by simp
    have hc2 : (if (addDag P Q).G.tgt (Sum.inr (false, true)) = Sum.inl (Sum.inr v) then
        (addDag P Q).polyLab (Sum.inr (false, true)) *
          (addDag P Q).G.valTo (addDag P Q).polyLab
            ((addDag P Q).G.src (Sum.inr (false, true))) else 0)
        = (if v = Q.G.s then 1 else 0) := by
      simp only [addDag_tgt_inr_false_true, addDag_polyLab_inr, addDag_src_inr_false,
        addDag_V_inlr_inj, one_mul]
      rw [addDag_valTo_src P Q]
      by_cases h : Q.G.s = v
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    have hc3 : (if (addDag P Q).G.tgt (Sum.inr (true, false)) = Sum.inl (Sum.inr v) then
        (addDag P Q).polyLab (Sum.inr (true, false)) *
          (addDag P Q).G.valTo (addDag P Q).polyLab
            ((addDag P Q).G.src (Sum.inr (true, false))) else 0) = 0 := by simp
    have hc4 : (if (addDag P Q).G.tgt (Sum.inr (true, true)) = Sum.inl (Sum.inr v) then
        (addDag P Q).polyLab (Sum.inr (true, true)) *
          (addDag P Q).G.valTo (addDag P Q).polyLab
            ((addDag P Q).G.src (Sum.inr (true, true))) else 0) = 0 := by simp
    rw [PathGraph.valTo_eq_sum_univ, PathGraph.valTo_eq_sum_univ Q.G,
      addDag_sum_edges (M := MvPolynomial ι F), Finset.sum_congr rfl (fun a _ => key a),
      Finset.sum_congr rfl (fun a _ => hzeroP a), hc1, hc2, hc3, hc4]
    simp only [addDag_s, addDag_V_inl_ne_inr, if_false, Finset.sum_const_zero, zero_add,
      add_zero]
    ring

/-- **Addition is computed correctly.** -/
theorem addDag_value : (addDag P Q).value = P.value + Q.value := by
  have hP : ∀ a : P.E,
      (if (addDag P Q).G.tgt (Sum.inl (Sum.inl a)) = Sum.inr true then
          (addDag P Q).polyLab (Sum.inl (Sum.inl a)) *
            (addDag P Q).G.valTo (addDag P Q).polyLab
              ((addDag P Q).G.src (Sum.inl (Sum.inl a))) else 0) = 0 := by
    intro a; simp
  have hQ : ∀ a : Q.E,
      (if (addDag P Q).G.tgt (Sum.inl (Sum.inr a)) = Sum.inr true then
          (addDag P Q).polyLab (Sum.inl (Sum.inr a)) *
            (addDag P Q).G.valTo (addDag P Q).polyLab
              ((addDag P Q).G.src (Sum.inl (Sum.inr a))) else 0) = 0 := by
    intro a; simp
  have hc1 : (if (addDag P Q).G.tgt (Sum.inr (false, false)) = Sum.inr true then
      (addDag P Q).polyLab (Sum.inr (false, false)) *
        (addDag P Q).G.valTo (addDag P Q).polyLab
          ((addDag P Q).G.src (Sum.inr (false, false))) else 0) = 0 := by simp
  have hc2 : (if (addDag P Q).G.tgt (Sum.inr (false, true)) = Sum.inr true then
      (addDag P Q).polyLab (Sum.inr (false, true)) *
        (addDag P Q).G.valTo (addDag P Q).polyLab
          ((addDag P Q).G.src (Sum.inr (false, true))) else 0) = 0 := by simp
  have hc3 : (if (addDag P Q).G.tgt (Sum.inr (true, false)) = Sum.inr true then
      (addDag P Q).polyLab (Sum.inr (true, false)) *
        (addDag P Q).G.valTo (addDag P Q).polyLab
          ((addDag P Q).G.src (Sum.inr (true, false))) else 0) = P.value := by
    simp only [addDag_tgt_inr_true, addDag_polyLab_inr, addDag_src_inr_true_false, one_mul,
      if_pos rfl]
    rw [addDag_valTo_inl_inl P Q (P.G.rank P.G.t) _ rfl]
    rfl
  have hc4 : (if (addDag P Q).G.tgt (Sum.inr (true, true)) = Sum.inr true then
      (addDag P Q).polyLab (Sum.inr (true, true)) *
        (addDag P Q).G.valTo (addDag P Q).polyLab
          ((addDag P Q).G.src (Sum.inr (true, true))) else 0) = Q.value := by
    simp only [addDag_tgt_inr_true, addDag_polyLab_inr, addDag_src_inr_true_true, one_mul,
      if_pos rfl]
    rw [addDag_valTo_inl_inr P Q (Q.G.rank Q.G.t) _ rfl]
    rfl
  show (addDag P Q).G.valTo (addDag P Q).polyLab (Sum.inr true) = _
  rw [PathGraph.valTo_eq_sum_univ, addDag_sum_edges (M := MvPolynomial ι F),
    Finset.sum_congr rfl (fun a _ => hP a), Finset.sum_congr rfl (fun a _ => hQ a),
    hc1, hc2, hc3, hc4]
  simp

/-- **A single labelled edge computes its label.** -/
theorem leafDag_value (A : AffineForm ι F) :
    (leafDag A).value = A.eval (X : ι → MvPolynomial ι F) := by
  have hsrc : (leafDag A).G.valTo (leafDag A).polyLab false = 1 := by
    rw [PathGraph.valTo_eq_sum_univ, leafDag_sum_edges]
    rw [if_pos (show (false : Bool) = (leafDag A).G.s from rfl),
      if_neg (show ¬((leafDag A).G.tgt () = false) from by simp [leafDag])]
    exact add_zero 1
  show (leafDag A).G.valTo (leafDag A).polyLab true = _
  rw [PathGraph.valTo_eq_sum_univ, leafDag_sum_edges]
  rw [if_neg (show ¬((true : Bool) = (leafDag A).G.s) from by simp [leafDag]),
    if_pos (show (leafDag A).G.tgt () = true from rfl)]
  rw [show (leafDag A).G.src () = false from rfl, hsrc, mul_one, zero_add]
  rfl


end LabelledDag

/-! ## Formulas -/

/-- A binary division-free arithmetic formula. -/
inductive Formula (ι F : Type) where
  | var : ι → Formula ι F
  | const : F → Formula ι F
  | add : Formula ι F → Formula ι F → Formula ι F
  | mul : Formula ι F → Formula ι F → Formula ι F

namespace Formula

/-- The polynomial computed by a formula. -/
noncomputable def eval : Formula ι F → MvPolynomial ι F
  | .var i => X i
  | .const c => C c
  | .add p q => p.eval + q.eval
  | .mul p q => p.eval * q.eval

/-- The number of leaves. -/
def leaves : Formula ι F → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add p q => p.leaves + q.leaves
  | .mul p q => p.leaves + q.leaves

/-- The number of addition gates. -/
def addGates : Formula ι F → ℕ
  | .var _ => 0
  | .const _ => 0
  | .add p q => p.addGates + q.addGates + 1
  | .mul p q => p.addGates + q.addGates

/-- The number of multiplication gates. -/
def mulGates : Formula ι F → ℕ
  | .var _ => 0
  | .const _ => 0
  | .add p q => p.mulGates + q.mulGates
  | .mul p q => p.mulGates + q.mulGates + 1

/-- The size of a formula. -/
def size (f : Formula ι F) : ℕ := f.leaves + f.addGates + f.mulGates

/-- The labelled DAG of a formula. -/
def toDag : Formula ι F → LabelledDag ι F
  | .var i => leafDag (varForm i)
  | .const c => leafDag ⟨c, []⟩
  | .add p q => addDag p.toDag q.toDag
  | .mul p q => mulDag p.toDag q.toDag

end Formula

end VNP1Char2
