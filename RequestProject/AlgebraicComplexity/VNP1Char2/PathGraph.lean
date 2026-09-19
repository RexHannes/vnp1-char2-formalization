/-
# A minimal finite labelled DAG model

We only build the structure the compiler actually needs:

* a finite vertex type `V` and a finite edge type `E`;
* source and target maps;
* distinguished `s ≠ t`;
* an explicit acyclicity witness: a rank function strictly increasing along edges.

A rank function is exactly a topological-order witness, so `rank_lt` *is* acyclicity
(`PathGraph.no_selfloop`, `PathGraph.walk_rank_lt`).  Parallel edges are allowed: `E` is an
arbitrary finite type mapped to `V` by `src` and `tgt`.

The value of the graph is defined by the usual dynamic program
`valTo v = [v = s] + ∑_{a : tgt a = v} ℓ a * valTo (src a)`,
which is the sum over all directed `s → v` paths of the product of the edge labels.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.BasicBoolean

namespace VNP1Char2

open scoped BigOperators

/-- A finite directed acyclic graph with a distinguished source and sink.
Acyclicity is witnessed by the strictly increasing `rank`. -/
structure PathGraph (V E : Type) where
  /-- source of an edge -/
  src : E → V
  /-- target of an edge -/
  tgt : E → V
  /-- the source vertex -/
  s : V
  /-- the sink vertex -/
  t : V
  /-- source and sink are distinct -/
  hst : s ≠ t
  /-- topological rank -/
  rank : V → ℕ
  /-- acyclicity witness -/
  rank_lt : ∀ a : E, rank (src a) < rank (tgt a)

namespace PathGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : PathGraph V E)

/-- No edge is a self-loop (immediate consequence of the rank witness). -/
theorem no_selfloop (a : E) : G.src a ≠ G.tgt a := fun h => by
  have h1 := G.rank_lt a
  rw [h] at h1
  exact lt_irrefl _ h1

/-- Edges entering `v`. -/
def inEdges (v : V) : Finset E := Finset.univ.filter fun a => G.tgt a = v

/-- Edges leaving `v`. -/
def outEdges (v : V) : Finset E := Finset.univ.filter fun a => G.src a = v

@[simp] theorem mem_inEdges {v : V} {a : E} : a ∈ G.inEdges v ↔ G.tgt a = v := by
  simp [inEdges]

@[simp] theorem mem_outEdges {v : V} {a : E} : a ∈ G.outEdges v ↔ G.src a = v := by
  simp [outEdges]

section Selection

variable (z : E → Bool)

/-- Selected edges entering `v`. -/
def selIn (v : V) : Finset E := (G.inEdges v).filter fun a => z a = true

/-- Selected edges leaving `v`. -/
def selOut (v : V) : Finset E := (G.outEdges v).filter fun a => z a = true

@[simp] theorem mem_selIn {v : V} {a : E} : a ∈ G.selIn z v ↔ G.tgt a = v ∧ z a = true := by
  simp [selIn]

@[simp] theorem mem_selOut {v : V} {a : E} : a ∈ G.selOut z v ↔ G.src a = v ∧ z a = true := by
  simp [selOut]

/-- The *raw* constraint system imposed by the selector polynomial `V_G`:
at most one selected edge on each side of each vertex (pair exclusions), odd selected
out-degree at the source, odd selected in-degree at the sink, and even selected total
degree at every internal vertex.

These are exactly the conditions `V_G(z) = 1`; see `PathPolynomial`. -/
def IsSelected : Prop :=
  (∀ v, (G.selIn z v).card ≤ 1) ∧
  (∀ v, (G.selOut z v).card ≤ 1) ∧
  (G.selOut z G.s).card % 2 = 1 ∧
  (G.selIn z G.t).card % 2 = 1 ∧
  (∀ v, v ≠ G.s → v ≠ G.t → ((G.selIn z v).card + (G.selOut z v).card) % 2 = 0)

/-- The *clean* description of an `s → v` path by its edge-incidence vector: no selected
edge enters the source, none leaves `v`, the selected in- and out-degrees agree at every
other vertex, and (unless `v = s`) exactly one selected edge leaves `s` and exactly one
enters `v`. -/
def IsPathSel (v : V) : Prop :=
  (∀ w, (G.selIn z w).card ≤ 1) ∧
  (∀ w, (G.selOut z w).card ≤ 1) ∧
  (G.selIn z G.s).card = 0 ∧
  (G.selOut z v).card = 0 ∧
  (∀ w, w ≠ G.s → w ≠ v → (G.selIn z w).card = (G.selOut z w).card) ∧
  (G.s ≠ v → (G.selOut z G.s).card = 1) ∧
  (G.s ≠ v → (G.selIn z v).card = 1)

instance : DecidablePred (IsSelected G) := fun _ => by unfold IsSelected; infer_instance

instance (v : V) : DecidablePred (fun z => IsPathSel G z v) := fun _ => by
  unfold IsPathSel; infer_instance

end Selection

/-- Directed walks, as lists of edges. -/
def IsWalk : V → List E → V → Prop
  | u, [], w => u = w
  | u, a :: l, w => G.src a = u ∧ IsWalk (G.tgt a) l w

@[simp] theorem isWalk_nil {u w : V} : G.IsWalk u [] w ↔ u = w := Iff.rfl

@[simp] theorem isWalk_cons {u w : V} {a : E} {l : List E} :
    G.IsWalk u (a :: l) w ↔ G.src a = u ∧ G.IsWalk (G.tgt a) l w := Iff.rfl

/-- Along a walk the rank is non-decreasing, and strictly increasing on nonempty walks.
This is the formal content of "the DAG has no cycles". -/
theorem walk_rank_le {u w : V} : ∀ {l : List E}, G.IsWalk u l w → G.rank u ≤ G.rank w := by
  intro l
  induction l generalizing u with
  | nil => intro h; exact le_of_eq (congrArg G.rank h)
  | cons a l ih =>
      intro h
      obtain ⟨h1, h2⟩ := h
      have h4 := G.rank_lt a
      have h3 := ih h2
      subst h1
      omega

/-- A nonempty walk strictly increases the rank: in particular there are no closed walks. -/
theorem walk_rank_lt {u w : V} {a : E} {l : List E} (h : G.IsWalk u (a :: l) w) :
    G.rank u < G.rank w := by
  obtain ⟨h1, h2⟩ := h
  have h3 := G.rank_lt a
  have h4 := G.walk_rank_le h2
  subst h1
  omega

section Value

variable {M : Type*} [CommRing M]

/-- The dynamic program computing, for each vertex `v`, the sum over all directed `s → v`
paths of the product of the edge labels. -/
noncomputable def valTo (G : PathGraph V E) (l : E → M) (v : V) : M :=
  (if v = G.s then 1 else 0) +
    ∑ a : {a : E // G.tgt a = v}, l a.1 * valTo G l (G.src a.1)
termination_by G.rank v
decreasing_by
  have h := a.2
  have hr := G.rank_lt a.1
  rw [h] at hr
  exact hr

/-- Unfolding lemma for `valTo`, phrased with `inEdges`. -/
theorem valTo_eq (G : PathGraph V E) (l : E → M) (v : V) :
    valTo G l v = (if v = G.s then 1 else 0) + ∑ a ∈ G.inEdges v, l a * valTo G l (G.src a) := by
  rw [valTo]
  congr 1
  exact (Finset.sum_subtype (p := fun a => G.tgt a = v) (G.inEdges v) (fun x => by simp)
    (fun a => l a * valTo G l (G.src a))).symm

/-- The polynomial computed by the graph: the sum over all `s → t` paths of the product of
the edge labels. -/
noncomputable def val (G : PathGraph V E) (l : E → M) : M := valTo G l G.t

end Value

end PathGraph

end VNP1Char2
