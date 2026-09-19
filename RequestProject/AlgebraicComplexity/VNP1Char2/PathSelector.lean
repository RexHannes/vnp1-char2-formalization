/-
# The path-selector theorem

The constraint system `IsSelected` (pair exclusions at *every* vertex, odd selected
out-degree at `s`, odd selected in-degree at `t`, even selected total degree at every
internal vertex) is satisfied exactly by the edge-incidence vectors of directed `s → t`
paths.

Acyclicity is used in an essential way, twice.

* A global counting argument shows that the selected in-degree of `s` equals the selected
  out-degree of `t`.  If these were `1`, then *every* vertex with a selected incoming edge
  would also have a selected outgoing edge, and following selected edges forward would
  produce a strictly rank-increasing infinite chain
  (`no_selected_edge_of_forward_closed`).  This is what rules out a selected directed
  cycle, and also the configuration "path from `s` to `t` plus a path from `t` back to
  `s`".
* The same device, run backwards, rules out extra selected components disjoint from the
  `s → t` path (`exists_walk_of_isPathSel`).
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.PathGraph

namespace VNP1Char2

namespace PathGraph

open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : PathGraph V E) (z : E → Bool)

theorem selIn_card_pos {v : V} {a : E} (ha : G.tgt a = v) (hz : z a = true) :
    1 ≤ (G.selIn z v).card :=
  Finset.card_pos.mpr ⟨a, by rw [mem_selIn]; exact ⟨ha, hz⟩⟩

theorem selOut_card_pos {v : V} {a : E} (ha : G.src a = v) (hz : z a = true) :
    1 ≤ (G.selOut z v).card :=
  Finset.card_pos.mpr ⟨a, by rw [mem_selOut]; exact ⟨ha, hz⟩⟩

/-- The total number of selected edges, counted by their targets. -/
theorem sum_selIn_card :
    (∑ v : V, (G.selIn z v).card) = (Finset.univ.filter fun a => z a = true).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := G.tgt) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun v _ => by congr 1; ext a; simp [selIn, inEdges, and_comm]

/-- The total number of selected edges, counted by their sources. -/
theorem sum_selOut_card :
    (∑ v : V, (G.selOut z v).card) = (Finset.univ.filter fun a => z a = true).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := G.src) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun v _ => by congr 1; ext a; simp [selOut, outEdges, and_comm]

/-- Global counting: the selected in-degree of the source equals the selected out-degree
of the sink, as soon as every internal vertex is balanced. -/
theorem selIn_src_eq_selOut_tgt
    (hbal : ∀ v, v ≠ G.s → v ≠ G.t → (G.selIn z v).card = (G.selOut z v).card)
    (hs : (G.selOut z G.s).card = 1) (ht : (G.selIn z G.t).card = 1) :
    (G.selIn z G.s).card = (G.selOut z G.t).card := by
  have hsum : (∑ v : V, (G.selIn z v).card) = ∑ v : V, (G.selOut z v).card := by
    rw [sum_selIn_card, sum_selOut_card]
  have hts : G.t ∈ (Finset.univ : Finset V).erase G.s := by simp [Ne.symm G.hst]
  have e1 : ∀ f : V → ℕ, (∑ v : V, f v) =
      f G.s + (f G.t + ∑ v ∈ ((Finset.univ : Finset V).erase G.s).erase G.t, f v) := by
    intro f
    rw [Finset.add_sum_erase _ f hts, Finset.add_sum_erase _ f (Finset.mem_univ G.s)]
  rw [e1 (fun v => (G.selIn z v).card), e1 (fun v => (G.selOut z v).card)] at hsum
  have hrest : (∑ v ∈ ((Finset.univ : Finset V).erase G.s).erase G.t, (G.selIn z v).card)
      = ∑ v ∈ ((Finset.univ : Finset V).erase G.s).erase G.t, (G.selOut z v).card := by
    refine Finset.sum_congr rfl fun v hv => ?_
    simp only [Finset.mem_erase] at hv
    exact hbal v hv.2.1 hv.1
  omega

/-- **No selected chain can be extended forever**: if every vertex with a selected
incoming edge also has a selected outgoing edge, then no edge is selected at all.  This is
the exact point where acyclicity enters. -/
theorem no_selected_edge_of_forward_closed
    (h : ∀ v, 1 ≤ (G.selIn z v).card → 1 ≤ (G.selOut z v).card) (a : E) : z a = false := by
  by_contra hza
  have hza' : z a = true := by simpa using hza
  set N := Finset.univ.sup G.rank with hN
  have hle : ∀ v : V, G.rank v ≤ N := fun v => Finset.le_sup (Finset.mem_univ v)
  have key : ∀ k, ∀ v : V, N - G.rank v ≤ k → 1 ≤ (G.selIn z v).card → False := by
    intro k
    induction k with
    | zero =>
        intro v hk hv
        obtain ⟨b, hb⟩ := Finset.card_pos.mp (h v hv)
        rw [mem_selOut] at hb
        have h1 := G.rank_lt b
        rw [hb.1] at h1
        have h2 := hle (G.tgt b)
        omega
    | succ k ih =>
        intro v hk hv
        obtain ⟨b, hb⟩ := Finset.card_pos.mp (h v hv)
        rw [mem_selOut] at hb
        have h1 := G.rank_lt b
        rw [hb.1] at h1
        exact ih (G.tgt b) (by omega) (selIn_card_pos G z rfl hb.2)
  exact key N (G.tgt a) (Nat.sub_le _ _) (selIn_card_pos G z rfl hza')

/-- Dually: if every vertex with a selected outgoing edge also has a selected incoming
edge, then no edge is selected. -/
theorem no_selected_edge_of_backward_closed
    (h : ∀ v, 1 ≤ (G.selOut z v).card → 1 ≤ (G.selIn z v).card) (a : E) : z a = false := by
  by_contra hza
  have hza' : z a = true := by simpa using hza
  have key : ∀ k, ∀ v : V, G.rank v ≤ k → 1 ≤ (G.selOut z v).card → False := by
    intro k
    induction k with
    | zero =>
        intro v hk hv
        obtain ⟨b, hb⟩ := Finset.card_pos.mp (h v hv)
        rw [mem_selIn] at hb
        have h1 := G.rank_lt b
        rw [hb.1] at h1
        exact absurd h1 (by omega)
    | succ k ih =>
        intro v hk hv
        obtain ⟨b, hb⟩ := Finset.card_pos.mp (h v hv)
        rw [mem_selIn] at hb
        have h1 := G.rank_lt b
        rw [hb.1] at h1
        exact ih (G.src b) (by omega) (selOut_card_pos G z rfl hb.2)
  exact key (G.rank (G.src a)) (G.src a) le_rfl (selOut_card_pos G z rfl hza')

/-- **Hard direction of the repair**: the raw constraint system forces the source to have
no selected incoming edge and the sink no selected outgoing edge, so that the selected set
is exactly described by the clean path conditions. -/
theorem isPathSel_of_isSelected (h : G.IsSelected z) : G.IsPathSel z G.t := by
  obtain ⟨pIn, pOut, hsrc, hsink, hint⟩ := h
  have hs : (G.selOut z G.s).card = 1 := by have := pOut G.s; omega
  have ht : (G.selIn z G.t).card = 1 := by have := pIn G.t; omega
  have hbal : ∀ v, v ≠ G.s → v ≠ G.t → (G.selIn z v).card = (G.selOut z v).card := by
    intro v h1 h2
    have := pIn v; have := pOut v; have := hint v h1 h2; omega
  have heq : (G.selIn z G.s).card = (G.selOut z G.t).card :=
    selIn_src_eq_selOut_tgt G z hbal hs ht
  have hzero : (G.selIn z G.s).card = 0 := by
    by_contra hne
    have h1 : (G.selIn z G.s).card = 1 := by have := pIn G.s; omega
    have h2 : (G.selOut z G.t).card = 1 := by omega
    have fc : ∀ v, 1 ≤ (G.selIn z v).card → 1 ≤ (G.selOut z v).card := by
      intro v hv
      by_cases hvs : v = G.s
      · subst hvs; omega
      · by_cases hvt : v = G.t
        · subst hvt; omega
        · rw [← hbal v hvs hvt]; exact hv
    have hempty : (G.selIn z G.t).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro a ha
      rw [mem_selIn] at ha
      rw [no_selected_edge_of_forward_closed G z fc a] at ha
      exact Bool.false_ne_true ha.2
    omega
  exact ⟨pIn, pOut, hzero, by omega, hbal, fun _ => hs, fun _ => ht⟩

/-- Conversely the clean path conditions imply the raw constraint system. -/
theorem isSelected_of_isPathSel (h : G.IsPathSel z G.t) : G.IsSelected z := by
  obtain ⟨pIn, pOut, hsIn, htOut, hbal, hsOut, htIn⟩ := h
  refine ⟨pIn, pOut, by rw [hsOut G.hst], by rw [htIn G.hst], fun v h1 h2 => ?_⟩
  rw [hbal v h1 h2]
  omega

/-- **Raw constraints are equivalent to the clean path conditions.** -/
theorem isSelected_iff_isPathSel : G.IsSelected z ↔ G.IsPathSel z G.t :=
  ⟨isPathSel_of_isSelected G z, isSelected_of_isPathSel G z⟩

end PathGraph

namespace PathGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : PathGraph V E)

theorem isWalk_append {u w x : V} {l1 l2 : List E} (h1 : G.IsWalk u l1 w)
    (h2 : G.IsWalk w l2 x) : G.IsWalk u (l1 ++ l2) x := by
  induction l1 generalizing u with
  | nil => cases h1; exact h2
  | cons a l ih => exact ⟨h1.1, ih h1.2⟩

theorem selIn_update_false (z : E → Bool) (a : E) (w : V) :
    G.selIn (Function.update z a false) w = (G.selIn z w).erase a := by
  ext b
  simp only [mem_selIn, Finset.mem_erase, Function.update_apply]
  by_cases h : b = a <;> simp [h]

theorem selOut_update_false (z : E → Bool) (a : E) (w : V) :
    G.selOut (Function.update z a false) w = (G.selOut z w).erase a := by
  ext b
  simp only [mem_selOut, Finset.mem_erase, Function.update_apply]
  by_cases h : b = a <;> simp [h]

/-- The empty selection is the only one satisfying the clean path conditions at `s`
(the `s → s` path is the empty path: this is again acyclicity). -/
theorem eq_false_of_isPathSel_src {z : E → Bool} (h : G.IsPathSel z G.s) (a : E) :
    z a = false := by
  obtain ⟨pIn, pOut, hsIn, hsOut, hbal, -, -⟩ := h
  refine no_selected_edge_of_forward_closed G z (fun w hw => ?_) a
  by_cases hws : w = G.s
  · subst hws; omega
  · rw [← hbal w hws hws]; exact hw

/-- Removing the last edge `a` of a path ending at `v` leaves a path ending at `src a`. -/
theorem isPathSel_update_false {z : E → Bool} {v : V} {a : E} (h : G.IsPathSel z v)
    (hsv : G.s ≠ v) (hat : G.tgt a = v) (haz : z a = true) :
    G.IsPathSel (Function.update z a false) (G.src a) := by
  obtain ⟨pIn, pOut, hsIn, hvOut, hbal, hsOut, hvIn⟩ := h
  set u := G.src a with hu
  have hrank : G.rank u < G.rank v := by
    have := G.rank_lt a; rw [hat] at this; exact this
  have huv : u ≠ v := fun hc => by rw [hc] at hrank; omega
  have hIn : ∀ w, G.selIn (Function.update z a false) w = (G.selIn z w).erase a :=
    selIn_update_false G z a
  have hOut : ∀ w, G.selOut (Function.update z a false) w = (G.selOut z w).erase a :=
    selOut_update_false G z a
  have haOut : a ∈ G.selOut z u := by rw [mem_selOut]; exact ⟨rfl, haz⟩
  have hcardOutu : (G.selOut z u).card = 1 := by
    have := pOut u; have := Finset.card_pos.mpr ⟨a, haOut⟩; omega
  have hInu : u ≠ G.s → (G.selIn z u).card = 1 := fun hus => by
    rw [hbal u hus huv, hcardOutu]
  have hanotIn : ∀ w, w ≠ v → a ∉ G.selIn z w := by
    intro w hw hc; rw [mem_selIn] at hc; exact hw (hat ▸ hc.1).symm
  have hanotOut : ∀ w, w ≠ u → a ∉ G.selOut z w := by
    intro w hw hc; rw [mem_selOut] at hc; exact hw hc.1.symm
  refine ⟨fun w => ?_, fun w => ?_, ?_, ?_, fun w hws hwu => ?_, fun hsu => ?_, fun hsu => ?_⟩
  · rw [hIn w]; exact le_trans Finset.card_erase_le (pIn w)
  · rw [hOut w]; exact le_trans Finset.card_erase_le (pOut w)
  · rw [hIn G.s]
    have h1 := Finset.card_erase_le (s := G.selIn z G.s) (a := a)
    omega
  · rw [hOut u, Finset.card_erase_of_mem haOut, hcardOutu]
  · rw [hIn w, hOut w, Finset.erase_eq_of_notMem (hanotOut w hwu)]
    by_cases hwv : w = v
    · subst hwv
      rw [Finset.card_erase_of_mem (by rw [mem_selIn]; exact ⟨hat, haz⟩), hvOut, hvIn hsv]
    · rw [Finset.erase_eq_of_notMem (hanotIn w hwv)]
      exact hbal w hws hwv
  · rw [hOut G.s, Finset.erase_eq_of_notMem (hanotOut G.s hsu), hsOut hsv]
  · rw [hIn u, Finset.erase_eq_of_notMem (hanotIn u huv), hInu (Ne.symm hsu)]

/-- **Extraction of the path.**  A selection satisfying the clean path conditions at `v`
is the edge-incidence vector of a directed walk from `s` to `v`; in particular no extra
selected edges, components or cycles survive. -/
theorem exists_walk_of_isPathSel : ∀ (v : V) (z : E → Bool), G.IsPathSel z v →
    ∃ l : List E, G.IsWalk G.s l v ∧ ∀ a, z a = true ↔ a ∈ l := by
  have base : ∀ (z : E → Bool), G.IsPathSel z G.s →
      ∃ l : List E, G.IsWalk G.s l G.s ∧ ∀ a, z a = true ↔ a ∈ l := by
    intro z h
    exact ⟨[], rfl, fun a => by simp [eq_false_of_isPathSel_src G h a]⟩
  have key : ∀ n (v : V) (z : E → Bool), G.rank v ≤ n → G.IsPathSel z v →
      ∃ l : List E, G.IsWalk G.s l v ∧ ∀ a, z a = true ↔ a ∈ l := by
    intro n
    induction n with
    | zero =>
        intro v z hr h
        by_cases hv : v = G.s
        · subst hv; exact base z h
        · exfalso
          obtain ⟨-, -, -, -, -, -, hvIn⟩ := h
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hvIn (fun hc => hv hc.symm))
          have hm : a ∈ G.selIn z v := by rw [ha]; exact Finset.mem_singleton_self a
          rw [mem_selIn] at hm
          have h2 := G.rank_lt a
          rw [hm.1] at h2
          omega
    | succ n ih =>
        intro v z hr h
        by_cases hv : v = G.s
        · subst hv; exact base z h
        obtain ⟨pIn, pOut, hsIn, hvOut, hbal, hsOut, hvIn⟩ := h
        have hsv : G.s ≠ v := fun hc => hv hc.symm
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hvIn hsv)
        have hamem : a ∈ G.selIn z v := by rw [ha]; exact Finset.mem_singleton_self a
        rw [mem_selIn] at hamem
        obtain ⟨hat, haz⟩ := hamem
        set u := G.src a with hu
        have hrank : G.rank u < G.rank v := by
          have := G.rank_lt a; rw [hat] at this; exact this
        have huv : u ≠ v := fun hc => by rw [hc] at hrank; omega
        set z' := Function.update z a false with hz'
        have hpath' : G.IsPathSel z' u :=
          isPathSel_update_false G ⟨pIn, pOut, hsIn, hvOut, hbal, hsOut, hvIn⟩ hsv hat haz
        obtain ⟨l', hwalk', hz'l⟩ := ih u z' (by omega) hpath'
        refine ⟨l' ++ [a], isWalk_append G hwalk' ⟨rfl, hat⟩, fun b => ?_⟩
        by_cases hb : b = a
        · subst hb; simp [haz]
        · have hzz : z' b = z b := by rw [hz']; simp [hb]
          rw [← hzz, hz'l b]
          simp [hb]
  intro v z h
  exact key (G.rank v) v z le_rfl h

theorem walk_mem_tgt_rank_le {u w : V} : ∀ {l : List E}, G.IsWalk u l w → ∀ {a : E}, a ∈ l →
    G.rank (G.tgt a) ≤ G.rank w := by
  intro l
  induction l generalizing u with
  | nil => intro _ a ha; simp at ha
  | cons b l ih =>
      intro h a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact G.walk_rank_le h.2
      · exact ih h.2 ha'

/-- A path ending at `v` has no selected edge at any vertex of larger rank. -/
theorem selIn_selOut_eq_empty_of_rank_lt {z : E → Bool} {v w : V} (h : G.IsPathSel z v)
    (hr : G.rank v < G.rank w) : G.selIn z w = ∅ ∧ G.selOut z w = ∅ := by
  obtain ⟨l, hl, hzl⟩ := exists_walk_of_isPathSel G v z h
  refine ⟨?_, ?_⟩ <;> rw [Finset.eq_empty_iff_forall_notMem] <;> intro a ha
  · rw [mem_selIn] at ha
    have := walk_mem_tgt_rank_le G hl ((hzl a).mp ha.2)
    rw [ha.1] at this; omega
  · rw [mem_selOut] at ha
    have h1 := walk_mem_tgt_rank_le G hl ((hzl a).mp ha.2)
    have h2 := G.rank_lt a
    rw [ha.1] at h2; omega

theorem rank_src_le_of_isPathSel {z : E → Bool} {v : V} (h : G.IsPathSel z v) :
    G.rank G.s ≤ G.rank v := by
  obtain ⟨l, hl, -⟩ := exists_walk_of_isPathSel G v z h
  exact G.walk_rank_le hl

theorem selIn_update_true (z : E → Bool) (a : E) (w : V) :
    G.selIn (Function.update z a true) w =
      if G.tgt a = w then insert a (G.selIn z w) else G.selIn z w := by
  ext b
  by_cases hw : G.tgt a = w <;>
    simp only [hw, if_true, if_false, mem_selIn, Finset.mem_insert, Function.update_apply] <;>
    by_cases hb : b = a <;> simp [hb, hw]

theorem selOut_update_true (z : E → Bool) (a : E) (w : V) :
    G.selOut (Function.update z a true) w =
      if G.src a = w then insert a (G.selOut z w) else G.selOut z w := by
  ext b
  by_cases hw : G.src a = w <;>
    simp only [hw, if_true, if_false, mem_selOut, Finset.mem_insert, Function.update_apply] <;>
    by_cases hb : b = a <;> simp [hb, hw]

/-- Appending the edge `a` to a path ending at `src a` yields a path ending at `tgt a`. -/
theorem isPathSel_update_true {z : E → Bool} {a : E} (h : G.IsPathSel z (G.src a)) :
    G.IsPathSel (Function.update z a true) (G.tgt a) := by
  obtain ⟨pIn, pOut, hsIn, huOut, hbal, hsOut, huIn⟩ := h
  have hrank := G.rank_lt a
  have hloop : G.src a ≠ G.tgt a := G.no_selfloop a
  have hvs : G.tgt a ≠ G.s := by
    have := rank_src_le_of_isPathSel G ⟨pIn, pOut, hsIn, huOut, hbal, hsOut, huIn⟩
    intro hc; rw [hc] at hrank; omega
  obtain ⟨hIv, hOv⟩ := selIn_selOut_eq_empty_of_rank_lt G
    ⟨pIn, pOut, hsIn, huOut, hbal, hsOut, huIn⟩ hrank
  have hOu : G.selOut z (G.src a) = ∅ := Finset.card_eq_zero.mp huOut
  have hIn := selIn_update_true G z a
  have hOut := selOut_update_true G z a
  refine ⟨fun w => ?_, fun w => ?_, ?_, ?_, fun w hws hwv => ?_, fun _ => ?_, fun _ => ?_⟩
  · rw [hIn w]
    by_cases hw : G.tgt a = w
    · subst hw; simp [hIv]
    · simp [hw, pIn w]
  · rw [hOut w]
    by_cases hw : G.src a = w
    · subst hw; simp [hOu]
    · simp [hw, pOut w]
  · rw [hIn G.s, if_neg hvs, hsIn]
  · rw [hOut (G.tgt a), if_neg hloop, hOv, Finset.card_empty]
  · rw [hIn w, hOut w, if_neg (Ne.symm hwv)]
    by_cases hw : G.src a = w
    · subst hw
      rw [if_pos rfl, hOu, huIn (Ne.symm hws)]
      simp
    · rw [if_neg hw]
      exact hbal w hws (Ne.symm hw)
  · rw [hOut G.s]
    by_cases hw : G.src a = G.s
    · rw [if_pos hw, ← hw, hOu]; simp
    · rw [if_neg hw, hsOut (Ne.symm hw)]
  · rw [hIn (G.tgt a), if_pos rfl, hIv]; simp

/-- An edge leaving the endpoint of a path is not selected. -/
theorem eq_false_of_isPathSel_src_edge {z : E → Bool} {a : E} (h : G.IsPathSel z (G.src a)) :
    z a = false := by
  by_contra hc
  have hm : a ∈ G.selOut z (G.src a) := by rw [mem_selOut]; exact ⟨rfl, by simpa using hc⟩
  rw [Finset.card_eq_zero.mp h.2.2.2.1] at hm
  simp at hm

end PathGraph

end VNP1Char2
