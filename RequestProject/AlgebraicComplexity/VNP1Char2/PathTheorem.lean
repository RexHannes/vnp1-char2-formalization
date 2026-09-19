/-
# (PATH): the selector polynomial is the indicator of the `s → t` paths

`selectorVal F G z` is the product of

* the flow factors (one per vertex),
* the pair-exclusion factors `1 + z_a z_b` over all ordered pairs of distinct edges sharing
  a head, and all ordered pairs of distinct edges sharing a tail — *including* at the source
  and at the sink, which is exactly what rules out three selected edges leaving the source.

This file proves that `selectorVal F G z = 1` holds **iff** the selected edges are exactly
the edges of a directed walk from `s` to `t`.  Acyclicity (the rank function) is what rules
out extra selected cycles or extra components: a selected component disjoint from the
`s → t` path would have to contain a vertex with a selected incoming edge but no selected
outgoing edge, contradicting the parity constraints — this is
`no_selected_edge_of_forward_closed` in `PathSelector`.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.PathPolynomial

namespace VNP1Char2

namespace PathGraph

open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : PathGraph V E)

theorem isWalk_snoc_iff {u v : V} {l : List E} {a : E} :
    G.IsWalk u (l ++ [a]) v ↔ G.IsWalk u l (G.src a) ∧ G.tgt a = v := by
  induction l generalizing u with
  | nil =>
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
  | cons b l ih =>
      rw [List.cons_append, isWalk_cons, ih, isWalk_cons, and_assoc]

theorem isPathSel_false_src : G.IsPathSel (fun _ => false) G.s := by
  have hIn : ∀ w, G.selIn (fun _ => false) w = ∅ := by
    intro w; ext a; simp [selIn]
  have hOut : ∀ w, G.selOut (fun _ => false) w = ∅ := by
    intro w; ext a; simp [selOut]
  refine ⟨fun w => by simp [hIn w], fun w => by simp [hOut w], by simp [hIn], by simp [hOut],
    fun w _ _ => by simp [hIn w, hOut w], fun h => absurd rfl h, fun h => absurd rfl h⟩

/-- **The edge set of a directed walk out of the source satisfies the clean path
conditions.**  This is the converse of `exists_walk_of_isPathSel`. -/
theorem isPathSel_of_isWalk : ∀ (l : List E) (v : V), G.IsWalk G.s l v →
    G.IsPathSel (fun a => decide (a ∈ l)) v := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      intro v h
      have : G.s = v := h
      subst this
      simpa using isPathSel_false_src G
  | append_singleton l a ih =>
      intro v h
      obtain ⟨hw, hv⟩ := (isWalk_snoc_iff G).mp h
      subst hv
      have hup : Function.update (fun b => decide (b ∈ l)) a true
          = fun b => decide (b ∈ l ++ [a]) := by
        funext b
        by_cases hb : b = a <;> simp [hb, Function.update_apply]
      rw [← hup]
      exact isPathSel_update_true G (ih (G.src a) hw)

/-- **(PATH)**  The selector polynomial equals `1` exactly when the selected edges are the
edges of a directed walk from the source to the sink; every such selection is a genuine
`s → t` path, and no other selection — in particular no selection containing an extra
cycle, an isolated selected edge, a disconnected component, several edges leaving the
source or several edges entering the sink — satisfies the constraints. -/
theorem path_selector_iff (F : Type*) [Field F] [CharP F 2] (z : E → Bool) :
    selectorVal F G z = 1 ↔ ∃ l : List E, G.IsWalk G.s l G.t ∧ ∀ a, z a = true ↔ a ∈ l := by
  rw [selectorVal_eq_one_iff, isSelected_iff_isPathSel]
  constructor
  · intro h
    exact exists_walk_of_isPathSel G G.t z h
  · rintro ⟨l, hl, hz⟩
    have hzl : z = fun a => decide (a ∈ l) := by
      funext a
      by_cases hmem : a ∈ l
      · simp only [hmem, decide_true, (hz a).mpr hmem]
      · have : z a ≠ true := fun hc => hmem ((hz a).mp hc)
        simp [hmem, Bool.eq_false_iff.mpr this]
    rw [hzl]
    exact isPathSel_of_isWalk G l G.t hl

end PathGraph

end VNP1Char2
