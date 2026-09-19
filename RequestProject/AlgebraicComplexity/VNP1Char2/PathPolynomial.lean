/-
# From the path selector to the graph polynomial

Part A of this file proves the *bridge*

```
∑_{z : E → Bool, z a path selection} ∏_{a selected} ℓ a  =  valTo G ℓ t,
```

i.e. the sum over the path-selection vectors of the product of the selected edge labels is
the dynamic-programming value of the graph.  The proof is an induction on the rank of the
endpoint: the summation over paths ending at `v` is split according to the (unique) last
edge, and removing that edge is a bijection onto the paths ending at its source.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.FourFactorIdentity
import RequestProject.AlgebraicComplexity.VNP1Char2.PathSelector

namespace VNP1Char2

namespace PathGraph

open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {M : Type*} [CommRing M] (G : PathGraph V E) (l : E → M)

/-- The product of the labels of the selected edges. -/
noncomputable def selProd (z : E → Bool) : M :=
  ∏ a ∈ Finset.univ.filter (fun a => z a = true), l a

theorem selProd_update_false {z : E → Bool} {a : E} (ha : z a = true) :
    selProd l z = l a * selProd l (Function.update z a false) := by
  have hset : (Finset.univ.filter (fun b => z b = true))
      = insert a (Finset.univ.filter (fun b => Function.update z a false b = true)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Function.update_apply]
    by_cases hb : b = a <;> simp [hb, ha]
  have hnot : a ∉ Finset.univ.filter (fun b => Function.update z a false b = true) := by simp
  rw [selProd, hset, Finset.prod_insert hnot, selProd]

/-- The sum, over all `s → v` paths, of the product of the edge labels, presented as a sum
over the edge-incidence vectors. -/
noncomputable def pathSum (v : V) : M :=
  ∑ z ∈ Finset.univ.filter (fun z => G.IsPathSel z v), selProd l z

/-- Removing the last edge is a bijection from the paths ending at `v` whose last edge is
`a` onto the paths ending at `src a`. -/
theorem pathSum_step {v : V} (hv : v ≠ G.s) {a : E} (ha : G.tgt a = v) :
    (∑ z ∈ (Finset.univ.filter (fun z => G.IsPathSel z v)).filter (fun z => z a = true),
      selProd l z) = l a * pathSum G l (G.src a) := by
  rw [pathSum, Finset.mul_sum]
  refine Finset.sum_nbij' (fun z => Function.update z a false) (fun z => Function.update z a true)
    ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact isPathSel_update_false G hz.1 (fun hc => hv hc.symm) ha hz.2
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    refine ⟨?_, by simp⟩
    have h2 := isPathSel_update_true G hz
    rwa [ha] at h2
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    funext b
    by_cases hb : b = a <;> simp [hb, Function.update_apply, hz.2]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    funext b
    by_cases hb : b = a
    · subst hb; simp [eq_false_of_isPathSel_src_edge G hz]
    · simp [hb]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact selProd_update_false l hz.2

/-- The paths ending at `v ≠ s` are classified by their last edge. -/
theorem pathSel_biUnion {v : V} (hv : v ≠ G.s) :
    Finset.univ.filter (fun z => G.IsPathSel z v)
      = (G.inEdges v).biUnion (fun a =>
          (Finset.univ.filter (fun z => G.IsPathSel z v)).filter (fun z => z a = true)) := by
  ext z
  simp only [Finset.mem_biUnion, mem_inEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (h.2.2.2.2.2.2 (fun hc => hv hc.symm))
    have hm : a ∈ G.selIn z v := ha ▸ Finset.mem_singleton_self a
    rw [mem_selIn] at hm
    exact ⟨a, hm.1, h, hm.2⟩
  · rintro ⟨a, -, h, -⟩; exact h

theorem pathSel_pairwiseDisjoint {v : V} :
    (↑(G.inEdges v) : Set E).PairwiseDisjoint (fun a =>
      (Finset.univ.filter (fun z => G.IsPathSel z v)).filter (fun z => z a = true)) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, mem_inEdges] at ha hb
  refine Finset.disjoint_left.mpr ?_
  intro z hza hzb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hza hzb
  have h1 : a ∈ G.selIn z v := by rw [mem_selIn]; exact ⟨ha, hza.2⟩
  have h2 : b ∈ G.selIn z v := by rw [mem_selIn]; exact ⟨hb, hzb.2⟩
  have hc := Finset.one_lt_card.mpr ⟨a, h1, b, h2, hab⟩
  have := hza.1.1 v
  omega

/-- Vertices of rank below the source are unreachable, so the dynamic program vanishes
there. -/
theorem valTo_eq_zero_of_rank_lt : ∀ (n : ℕ) (v : V), G.rank v ≤ n → G.rank v < G.rank G.s →
    valTo G l v = 0 := by
  intro n
  induction n with
  | zero =>
      intro v hn hv
      rw [valTo_eq, if_neg (by rintro rfl; omega)]
      have hempty : G.inEdges v = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [mem_inEdges] at ha
        have := G.rank_lt a
        rw [ha] at this
        omega
      rw [hempty]
      simp
  | succ n ih =>
      intro v hn hv
      rw [valTo_eq, if_neg (by rintro rfl; omega)]
      have hz : ∀ a ∈ G.inEdges v, l a * valTo G l (G.src a) = 0 := by
        intro a ha
        rw [mem_inEdges] at ha
        have h1 := G.rank_lt a
        rw [ha] at h1
        rw [ih (G.src a) (by omega) (by omega), mul_zero]
      rw [Finset.sum_congr rfl hz]
      simp

/-- The all-false selection is a path selection at the source, and it is the only one. -/
theorem isPathSel_false : G.IsPathSel (fun _ => false) G.s := by
  have h : ∀ w, G.selIn (fun _ => false) w = ∅ ∧ G.selOut (fun _ => false) w = ∅ := by
    intro w
    constructor <;> rw [Finset.eq_empty_iff_forall_notMem] <;> intro a ha <;>
      simp [mem_selIn, mem_selOut] at ha
  exact ⟨fun w => by rw [(h w).1]; simp, fun w => by rw [(h w).2]; simp, by rw [(h G.s).1]; simp,
    by rw [(h G.s).2]; simp, fun w _ _ => by rw [(h w).1, (h w).2], fun hc => absurd rfl hc,
    fun hc => absurd rfl hc⟩

theorem pathSel_src_eq : Finset.univ.filter (fun z => G.IsPathSel z G.s) = {fun _ => false} := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => funext fun b => eq_false_of_isPathSel_src G h b, fun h => h ▸ isPathSel_false G⟩

/-- **The bridge.**  The sum over `s → v` path selections of the product of the selected
labels is the dynamic-programming value at `v`. -/
theorem pathSum_eq_valTo : ∀ (v : V), pathSum G l v = valTo G l v := by
  have key : ∀ (n : ℕ) (v : V), G.rank v ≤ n → pathSum G l v = valTo G l v := by
    intro n
    induction n with
    | zero =>
        intro v hn
        by_cases hv : v = G.s
        · subst hv
          rw [pathSum, pathSel_src_eq G, Finset.sum_singleton, valTo_eq, if_pos rfl]
          have hempty : G.inEdges G.s = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro a ha
            rw [mem_inEdges] at ha
            have := G.rank_lt a
            rw [ha] at this
            omega
          rw [hempty, selProd]
          simp
        · -- at rank `0` a vertex other than the source has no incoming edge, so there is no
          -- path ending there and both sides vanish
          have hin : G.inEdges v = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro a ha
            rw [mem_inEdges] at ha
            have := G.rank_lt a
            rw [ha] at this
            omega
          have hnone : Finset.univ.filter (fun z => G.IsPathSel z v) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
            obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hz.2.2.2.2.2.2 (fun hc => hv hc.symm))
            have hm : a ∈ G.selIn z v := ha ▸ Finset.mem_singleton_self a
            rw [mem_selIn] at hm
            have := G.rank_lt a
            rw [hm.1] at this
            omega
          rw [pathSum, hnone, Finset.sum_empty, valTo_eq, if_neg hv, hin]
          simp
    | succ n ih =>
        intro v hn
        by_cases hv : v = G.s
        · subst hv
          rw [pathSum, pathSel_src_eq G, Finset.sum_singleton, valTo_eq, if_pos rfl, selProd]
          have hz : ∀ a ∈ G.inEdges G.s, l a * valTo G l (G.src a) = 0 := by
            intro a ha
            rw [mem_inEdges] at ha
            have h1 := G.rank_lt a
            rw [ha] at h1
            rw [valTo_eq_zero_of_rank_lt G l (G.rank (G.src a)) (G.src a) le_rfl (by omega),
              mul_zero]
          rw [Finset.sum_congr rfl hz]
          simp
        · rw [valTo_eq, if_neg hv, zero_add, pathSum, pathSel_biUnion G hv,
            Finset.sum_biUnion (pathSel_pairwiseDisjoint G)]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [mem_inEdges] at ha
          have h1 := G.rank_lt a
          rw [ha] at h1
          rw [pathSum_step G l hv ha, ih (G.src a) (by omega)]
  exact fun v => key (G.rank v) v le_rfl


/-!
## Part B: the selector polynomial and the ABP identity

`V_G(z)` is the product of one flow factor per vertex and of the pair-exclusion factors
`1 + z_a z_b` for all ordered pairs of distinct edges sharing a head or a tail (ordered
pairs are used only for convenience: each unordered pair contributes twice, and the value
at a Boolean point is unchanged).
-/

section Selector

variable (F : Type*) [Field F] [CharP F 2]

theorem natCast_char_two (n : ℕ) : ((n : ℕ) : F) = if n % 2 = 0 then 0 else 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 2 ∧ n = 2 * k + r :=
    ⟨n / 2, n % 2, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r
  · push_cast; rw [if_pos (by omega)]; linear_combination (k : F) * h2
  · push_cast; rw [if_neg (by omega)]; linear_combination (k : F) * h2

theorem prod_eq_one_iff_of_zero_or_one {ι : Type*} (s : Finset ι) (f : ι → F)
    (h : ∀ i ∈ s, f i = 0 ∨ f i = 1) : (∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1 := by
  refine ⟨fun hp i hi => ?_, Finset.prod_eq_one⟩
  rcases h i hi with h0 | h1
  · rw [Finset.prod_eq_zero hi h0] at hp; exact absurd hp zero_ne_one
  · exact h1

theorem mul_eq_one_iff_of_zero_or_one {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    x * y = 1 ↔ x = 1 ∧ y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

variable (G : PathGraph V E) (z : E → Bool)

theorem sum_boolVal (S : Finset E) :
    (∑ a ∈ S, (boolVal (z a) : F)) = ((S.filter (fun a => z a = true)).card : F) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : z a <;> simp [boolVal]

theorem selIn_eq_filter (v : V) : G.selIn z v = (G.inEdges v).filter (fun a => z a = true) := rfl

theorem selOut_eq_filter (v : V) : G.selOut z v = (G.outEdges v).filter (fun a => z a = true) :=
  rfl

/-- The flow factor at a vertex: `∑_{out(s)} z` at the source, `∑_{in(t)} z` at the sink,
and `1 + ∑_{in(v)} z + ∑_{out(v)} z` at an internal vertex. -/
def flowFactor (v : V) : F :=
  if v = G.s then ∑ a ∈ G.outEdges G.s, (boolVal (z a) : F)
  else if v = G.t then ∑ a ∈ G.inEdges G.t, (boolVal (z a) : F)
  else 1 + (∑ a ∈ G.inEdges v, (boolVal (z a) : F) + ∑ a ∈ G.outEdges v, (boolVal (z a) : F))

/-- The pair-exclusion factors `1 + z_a z_b` over ordered pairs of distinct edges of `S`. -/
def pairFactors (S : Finset E) : F :=
  ∏ p ∈ S.offDiag, (1 + (boolVal (z p.1) : F) * boolVal (z p.2))

/-- The selector polynomial `V_G(z)`. -/
def selectorVal : F :=
  (∏ v : V, flowFactor F G z v) *
    ∏ v : V, (pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v))

theorem flowFactor_zero_or_one (v : V) : flowFactor F G z v = 0 ∨ flowFactor F G z v = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  unfold flowFactor
  split_ifs
  · rw [sum_boolVal, natCast_char_two]; split_ifs <;> simp
  · rw [sum_boolVal, natCast_char_two]; split_ifs <;> simp
  · rw [sum_boolVal, sum_boolVal, ← Nat.cast_add, natCast_char_two]
    split_ifs
    · right; simp
    · left; linear_combination h2

theorem flowFactor_eq_one_iff (v : V) : flowFactor F G z v = 1 ↔
    (if v = G.s then (G.selOut z G.s).card % 2 = 1
     else if v = G.t then (G.selIn z G.t).card % 2 = 1
     else ((G.selIn z v).card + (G.selOut z v).card) % 2 = 0) := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  unfold flowFactor
  simp only [selIn_eq_filter, selOut_eq_filter]
  split_ifs
  · rw [sum_boolVal, natCast_char_two]; split_ifs <;> simp <;> omega
  · rw [sum_boolVal, natCast_char_two]; split_ifs <;> simp <;> omega
  · rw [sum_boolVal, sum_boolVal, ← Nat.cast_add, natCast_char_two]
    split_ifs with h
    · simp [h]
    · exact ⟨fun hc => absurd (by linear_combination hc : (1 : F) = 0) one_ne_zero,
        fun hc => absurd hc h⟩

theorem pairFactor_zero_or_one (a b : E) :
    (1 + (boolVal (z a) : F) * boolVal (z b)) = 0 ∨ (1 + (boolVal (z a) : F) * boolVal (z b)) = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  cases h : z a
  · right; simp [boolVal]
  cases h' : z b
  · right; simp [boolVal]
  · left; simp only [boolVal, mul_one]; linear_combination h2

theorem pairFactors_zero_or_one (S : Finset E) :
    pairFactors F z S = 0 ∨ pairFactors F z S = 1 := by
  by_cases h : ∀ p ∈ S.offDiag, (1 + (boolVal (z p.1) : F) * boolVal (z p.2)) = 1
  · right; exact Finset.prod_eq_one h
  · left
    push_neg at h
    obtain ⟨p, hp, hp1⟩ := h
    exact Finset.prod_eq_zero hp ((pairFactor_zero_or_one F z p.1 p.2).resolve_right hp1)

theorem pairFactors_eq_one_iff (S : Finset E) :
    pairFactors F z S = 1 ↔ (S.filter (fun a => z a = true)).card ≤ 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  rw [pairFactors,
    prod_eq_one_iff_of_zero_or_one F _ _ (fun p _ => pairFactor_zero_or_one F z p.1 p.2),
    Finset.card_le_one]
  constructor
  · intro h a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hab
    have hp : (a, b) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨ha.1, hb.1, hab⟩
    have hval := h (a, b) hp
    rw [ha.2, hb.2] at hval
    simp only [boolVal, mul_one] at hval
    exact one_ne_zero (by linear_combination hval : (1 : F) = 0)
  · intro h p hp
    rw [Finset.mem_offDiag] at hp
    cases h1 : z p.1
    · simp [boolVal]
    cases h2' : z p.2
    · simp [boolVal]
    · exact absurd (h p.1 (Finset.mem_filter.mpr ⟨hp.1, h1⟩) p.2
        (Finset.mem_filter.mpr ⟨hp.2.1, h2'⟩)) hp.2.2

theorem selectorVal_zero_or_one : selectorVal F G z = 0 ∨ selectorVal F G z = 1 := by
  by_cases h : selectorVal F G z = 1
  · exact Or.inr h
  refine Or.inl ?_
  rw [selectorVal] at h ⊢
  have hA : (∏ v : V, flowFactor F G z v) = 0 ∨ (∏ v : V, flowFactor F G z v) = 1 := by
    by_cases hc : ∀ v ∈ (Finset.univ : Finset V), flowFactor F G z v = 1
    · exact Or.inr (Finset.prod_eq_one hc)
    · push_neg at hc
      obtain ⟨v, hv, hv1⟩ := hc
      exact Or.inl (Finset.prod_eq_zero hv ((flowFactor_zero_or_one F G z v).resolve_right hv1))
  have hB : (∏ v : V, (pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v))) = 0 ∨
      (∏ v : V, (pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v))) = 1 := by
    by_cases hc : ∀ v ∈ (Finset.univ : Finset V),
        pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v) = 1
    · exact Or.inr (Finset.prod_eq_one hc)
    · push_neg at hc
      obtain ⟨v, hv, hv1⟩ := hc
      refine Or.inl (Finset.prod_eq_zero hv ?_)
      rcases pairFactors_zero_or_one F z (G.inEdges v) with h0 | h1
      · rw [h0, zero_mul]
      · rcases pairFactors_zero_or_one F z (G.outEdges v) with h0' | h1'
        · rw [h0', mul_zero]
        · exact absurd (by rw [h1, h1', one_mul]) hv1
  rcases hA with hA | hA
  · rw [hA, zero_mul]
  rcases hB with hB | hB
  · rw [hB, mul_zero]
  · exact absurd (by rw [hA, hB, one_mul]) h

/-- **The selector polynomial is the indicator of the constraint system.** -/
theorem selectorVal_eq_one_iff : selectorVal F G z = 1 ↔ G.IsSelected z := by
  have hA : ∀ v ∈ (Finset.univ : Finset V), flowFactor F G z v = 0 ∨ flowFactor F G z v = 1 :=
    fun v _ => flowFactor_zero_or_one F G z v
  have hB : ∀ v ∈ (Finset.univ : Finset V),
      pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v) = 0 ∨
      pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v) = 1 := by
    intro v _
    rcases pairFactors_zero_or_one F z (G.inEdges v) with h0 | h1
    · exact Or.inl (by rw [h0, zero_mul])
    · rcases pairFactors_zero_or_one F z (G.outEdges v) with h0' | h1'
      · exact Or.inl (by rw [h0', mul_zero])
      · exact Or.inr (by rw [h1, h1', one_mul])
  rw [selectorVal, mul_eq_one_iff_of_zero_or_one F
      (by by_cases hc : ∀ v ∈ (Finset.univ : Finset V), flowFactor F G z v = 1
          · exact Or.inr (Finset.prod_eq_one hc)
          · push_neg at hc
            obtain ⟨v, hv, hv1⟩ := hc
            exact Or.inl (Finset.prod_eq_zero hv ((hA v hv).resolve_right hv1)))
      (by by_cases hc : ∀ v ∈ (Finset.univ : Finset V),
            pairFactors F z (G.inEdges v) * pairFactors F z (G.outEdges v) = 1
          · exact Or.inr (Finset.prod_eq_one hc)
          · push_neg at hc
            obtain ⟨v, hv, hv1⟩ := hc
            exact Or.inl (Finset.prod_eq_zero hv ((hB v hv).resolve_right hv1))),
    prod_eq_one_iff_of_zero_or_one F _ _ hA, prod_eq_one_iff_of_zero_or_one F _ _ hB]
  constructor
  · rintro ⟨hflow, hpair⟩
    have hpin : ∀ v, (G.selIn z v).card ≤ 1 := by
      intro v
      have := (mul_eq_one_iff_of_zero_or_one F (pairFactors_zero_or_one F z (G.inEdges v))
        (pairFactors_zero_or_one F z (G.outEdges v))).mp (hpair v (Finset.mem_univ v))
      rw [selIn_eq_filter]
      exact (pairFactors_eq_one_iff F z (G.inEdges v)).mp this.1
    have hpout : ∀ v, (G.selOut z v).card ≤ 1 := by
      intro v
      have := (mul_eq_one_iff_of_zero_or_one F (pairFactors_zero_or_one F z (G.inEdges v))
        (pairFactors_zero_or_one F z (G.outEdges v))).mp (hpair v (Finset.mem_univ v))
      rw [selOut_eq_filter]
      exact (pairFactors_eq_one_iff F z (G.outEdges v)).mp this.2
    refine ⟨hpin, hpout, ?_, ?_, ?_⟩
    · have := (flowFactor_eq_one_iff F G z G.s).mp (hflow G.s (Finset.mem_univ _))
      simpa using this
    · have := (flowFactor_eq_one_iff F G z G.t).mp (hflow G.t (Finset.mem_univ _))
      simpa [Ne.symm G.hst] using this
    · intro v h1 h2
      have := (flowFactor_eq_one_iff F G z v).mp (hflow v (Finset.mem_univ _))
      simpa [h1, h2] using this
  · rintro ⟨hpin, hpout, hs, ht, hint⟩
    constructor
    · intro v _
      rw [flowFactor_eq_one_iff]
      split_ifs with h1 h2
      · subst h1; exact hs
      · subst h2; exact ht
      · exact hint v h1 h2
    · intro v _
      rw [mul_eq_one_iff_of_zero_or_one F (pairFactors_zero_or_one F z (G.inEdges v))
        (pairFactors_zero_or_one F z (G.outEdges v))]
      exact ⟨(pairFactors_eq_one_iff F z (G.inEdges v)).mpr (by rw [← selIn_eq_filter]; exact hpin v),
        (pairFactors_eq_one_iff F z (G.outEdges v)).mpr (by rw [← selOut_eq_filter]; exact hpout v)⟩

end Selector

section ABP

variable {M : Type*} [CommRing M]
variable (G : PathGraph V E)

/-- The edge-weight selector `E_a(z, X) = 1 + z_a (ℓ_a(X) + 1)`. -/
def edgeSel (l : E → M) (z : E → Bool) (a : E) : M := 1 + boolVal (z a) * (l a + 1)

theorem edgeSel_of_false {l : E → M} {z : E → Bool} {a : E} (h : z a = false) :
    edgeSel l z a = 1 := by simp [edgeSel, h, boolVal]

theorem edgeSel_of_true (h2 : (2 : M) = 0) {l : E → M} {z : E → Bool} {a : E} (h : z a = true) :
    edgeSel l z a = l a := by
  simp only [edgeSel, h, boolVal, one_mul]
  linear_combination h2

theorem prod_edgeSel (h2 : (2 : M) = 0) (l : E → M) (z : E → Bool) :
    (∏ a : E, edgeSel l z a) = selProd l z := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun a => z a = true), selProd]
  have h1 : ∀ a ∈ Finset.univ.filter (fun a => z a = true), edgeSel l z a = l a := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact edgeSel_of_true h2 ha.2
  have h2 : ∀ a ∈ Finset.univ.filter (fun a => ¬ (z a = true)), edgeSel l z a = 1 := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact edgeSel_of_false (by simpa using ha.2)
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, Finset.prod_const_one, mul_one]

/-- **(ABP)** The graph polynomial is the Boolean-hypercube sum, over all edge selections,
of the selector polynomial times the edge-weight selectors.  This is a formal identity in
the original variables: only the `z`'s are specialised to Boolean values. -/
theorem abp_identity (F : Type*) [Field F] [CharP F 2] [Algebra F M] (l : E → M) :
    (∑ z : E → Bool, algebraMap F M (selectorVal F G z) * ∏ a : E, edgeSel l z a) = val G l := by
  classical
  have hzero : ∀ z ∈ (Finset.univ : Finset (E → Bool)),
      z ∉ Finset.univ.filter (fun z => G.IsSelected z) →
      algebraMap F M (selectorVal F G z) * ∏ a : E, edgeSel l z a = 0 := by
    intro z _ hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have : selectorVal F G z = 0 :=
      (selectorVal_zero_or_one F G z).resolve_right
        (fun hc => hz ((selectorVal_eq_one_iff F G z).mp hc))
    rw [this, map_zero, zero_mul]
  rw [← Finset.sum_subset (Finset.filter_subset (fun z => G.IsSelected z) Finset.univ) hzero]
  have hcongr : ∀ z ∈ Finset.univ.filter (fun z => G.IsSelected z),
      algebraMap F M (selectorVal F G z) * ∏ a : E, edgeSel l z a = selProd l z := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [(selectorVal_eq_one_iff F G z).mpr hz, map_one, one_mul,
      prod_edgeSel (two_eq_zero_of_algebra F) l z]
  rw [Finset.sum_congr rfl hcongr]
  have hset : Finset.univ.filter (fun z => G.IsSelected z)
      = Finset.univ.filter (fun z => G.IsPathSel z G.t) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isSelected_iff_isPathSel G z
  rw [hset, ← pathSum, pathSum_eq_valTo, val]

end ABP

end PathGraph

end VNP1Char2
