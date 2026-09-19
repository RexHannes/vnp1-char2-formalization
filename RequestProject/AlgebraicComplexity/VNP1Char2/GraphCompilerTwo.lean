/-
# Compiling a labelled DAG into a **support-two** affine-product hypercube representation

The support-three compiler of `GraphCompiler.lean` is left untouched; this file adds the
support-two compiler on top of the same graph data.

Two things change with respect to the support-three compiler.

* Every quadratic factor `1 + x y` (the edge selectors `E_a = 1 + z_a(ℓ_a+1)` and the pair
  exclusions `1 + z_a z_b`) is expanded by the **three-factor, one-auxiliary** gadget
  `gadget2Factors` instead of the four-factor, two-auxiliary gadget.
* A flow factor `1 + z_a + z_b + z_c` at an internal vertex of total degree three is itself
  of support three, so it must be expanded as well.  This is what `ternFactors` does, at
  the price of the cubic error `κ⁻¹ z_a z_b z_c`.

**Why the error is harmless, and why the order of the proof matters.**  At a vertex of
total degree three, two of the three incident edges share a head or share a tail (there are
only two sides), so the corresponding pair-exclusion factor `1 + z_a z_b` occurs in the
product.  For a *Boolean* selection `z` one has `z_a z_b z_c (1 + z_a z_b) = 0` in
characteristic two.  This is a pointwise statement about Boolean assignments: `a b c(1+ab)`
is **not** the zero polynomial (`cubic_error_not_formally_zero`).  Accordingly the error is
discharged through the hypothesis `hkill` of `compiled2_value`, i.e. after the selector
variables have been fixed to Boolean values and before the hypercube sum is performed.

Flow factors at the source, at the sink, and at internal vertices of total degree at most
two are already of support at most two and are used unchanged.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.CompilerTwo
import RequestProject.AlgebraicComplexity.VNP1Char2.SupportThree

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace VNP1Char2

namespace PathGraph

open scoped BigOperators
open AffineForm MvPolynomial

variable {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {F : Type*} [Field F] [CharP F 2]
variable (G : PathGraph V E) (lab : E → AffineForm ι F)

/-! ## The ternary data at a vertex of total degree three -/

/-- The data extracted at a vertex `v` of total degree three: three incident edges whose
selection variables are exactly the ones occurring in the flow factor at `v`, the **first
two of which share a head or share a tail** and are therefore constrained by a
pair-exclusion factor. -/
def TernTriple (v : V) (p : E × E × E) : Prop :=
  (∀ f : E → F, (∑ e ∈ G.inEdges v, f e) + (∑ e ∈ G.outEdges v, f e)
      = f p.1 + f p.2.1 + f p.2.2) ∧
    ((⟨v, (p.1, p.2.1)⟩ : (_ : V) × (E × E)) ∈ G.inPairs ∨
      (⟨v, (p.1, p.2.1)⟩ : (_ : V) × (E × E)) ∈ G.outPairs)

omit [CharP F 2] in
/-- **Pigeonhole at a degree-three vertex.**  Three incident edges are distributed over the
two sides of the vertex, so two of them share a head or share a tail. -/
theorem exists_ternTriple (v : V) (h3 : (G.inEdges v).card + (G.outEdges v).card = 3) :
    ∃ p : E × E × E, TernTriple (F := F) G v p := by
  have hcases : (G.inEdges v).card = 0 ∨ (G.inEdges v).card = 1 ∨ (G.inEdges v).card = 2 ∨
      (G.inEdges v).card = 3 := by omega
  rcases hcases with h | h | h | h
  · obtain ⟨a, b, c, hab, hac, hbc, hout⟩ :=
      Finset.card_eq_three.mp (show (G.outEdges v).card = 3 by omega)
    have hin : G.inEdges v = ∅ := Finset.card_eq_zero.mp h
    refine ⟨(a, b, c), ?_, Or.inr ?_⟩
    · intro f
      rw [hin, hout]
      simp only [Finset.sum_empty, zero_add, Finset.sum_insert, Finset.mem_insert,
        Finset.mem_singleton, hab, hac, hbc, or_self, not_false_eq_true, Finset.sum_singleton]
      ring
    · simp [outPairs, Finset.mem_sigma, Finset.mem_offDiag, hout, hab]
  · obtain ⟨c, hin⟩ := Finset.card_eq_one.mp h
    obtain ⟨a, b, hab, hout⟩ := Finset.card_eq_two.mp (show (G.outEdges v).card = 2 by omega)
    refine ⟨(a, b, c), ?_, Or.inr ?_⟩
    · intro f
      rw [hin, hout]
      simp only [Finset.sum_singleton, Finset.sum_insert, Finset.mem_singleton, hab,
        not_false_eq_true]
      ring
    · simp [outPairs, Finset.mem_sigma, Finset.mem_offDiag, hout, hab]
  · obtain ⟨a, b, hab, hin⟩ := Finset.card_eq_two.mp h
    obtain ⟨c, hout⟩ := Finset.card_eq_one.mp (show (G.outEdges v).card = 1 by omega)
    refine ⟨(a, b, c), ?_, Or.inl ?_⟩
    · intro f
      rw [hin, hout]
      simp only [Finset.sum_singleton, Finset.sum_insert, Finset.mem_singleton, hab,
        not_false_eq_true]
    · simp [inPairs, Finset.mem_sigma, Finset.mem_offDiag, hin, hab]
  · obtain ⟨a, b, c, hab, hac, hbc, hin⟩ := Finset.card_eq_three.mp h
    have hout : G.outEdges v = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨(a, b, c), ?_, Or.inl ?_⟩
    · intro f
      rw [hin, hout]
      simp only [Finset.sum_empty, add_zero, Finset.sum_insert, Finset.mem_insert,
        Finset.mem_singleton, hab, hac, hbc, or_self, not_false_eq_true, Finset.sum_singleton]
      ring
    · simp [inPairs, Finset.mem_sigma, Finset.mem_offDiag, hin, hab]

/-- The internal vertices whose flow factor has support three and therefore needs the
ternary gadget. -/
def ternVerts : Finset V :=
  Finset.univ.filter fun v =>
    v ≠ G.s ∧ v ≠ G.t ∧ (G.inEdges v).card + (G.outEdges v).card = 3

omit [DecidableEq E] in
@[simp] theorem mem_ternVerts {v : V} :
    v ∈ G.ternVerts ↔ v ≠ G.s ∧ v ≠ G.t ∧ (G.inEdges v).card + (G.outEdges v).card = 3 := by
  simp [ternVerts]

/-- The index type of the ternary gadget occurrences. -/
abbrev TernIdx : Type := {v // v ∈ G.ternVerts}

omit [CharP F 2] [DecidableEq E] in
@[simp] theorem card_ternIdx : Fintype.card G.TernIdx = G.ternVerts.card :=
  Fintype.card_coe _

/-- The three incident edges chosen at a degree-three internal vertex. -/
noncomputable def ternTripleOf (j : G.TernIdx) : E × E × E :=
  (exists_ternTriple (F := F) G j.1 (G.mem_ternVerts.mp j.2).2.2).choose

omit [CharP F 2] in
theorem ternTripleOf_spec (j : G.TernIdx) :
    TernTriple (F := F) G j.1 (ternTripleOf (F := F) G j) :=
  (exists_ternTriple (F := F) G j.1 (G.mem_ternVerts.mp j.2).2.2).choose_spec

/-- First edge of the ternary triple. -/
noncomputable def ternA (j : G.TernIdx) : E := (ternTripleOf (F := F) G j).1
/-- Second edge of the ternary triple; it shares a head or a tail with the first. -/
noncomputable def ternB (j : G.TernIdx) : E := (ternTripleOf (F := F) G j).2.1
/-- Third edge of the ternary triple. -/
noncomputable def ternC (j : G.TernIdx) : E := (ternTripleOf (F := F) G j).2.2

/-! ## The flow factors that stay affine -/

/-- The flow factors used as they are: the flow factor at every vertex that does not get a
ternary gadget, and the constant `1` at the vertices that do. -/
noncomputable def flowForms2 : List (AffineForm (ι ⊕ E) F) :=
  (Finset.univ : Finset V).toList.map fun v =>
    if v ∈ G.ternVerts then (⟨1, []⟩ : AffineForm (ι ⊕ E) F) else flowAff G v

omit [CharP F 2] [DecidableEq E] in
@[simp] theorem length_flowForms2 :
    (flowForms2 (ι := ι) (F := F) G).length = Fintype.card V := by
  simp [flowForms2]

/-- **The support-two compiled representation of a labelled DAG.** -/
noncomputable def graphRep2 (τ : F) : AffineHypercubeRep ι F :=
  compiled2 τ (flowForms2 G) (ternA (F := F) G) (ternB (F := F) G) (ternC (F := F) G)
    (gadgetX G lab) (gadgetY G)

/-! ## Value -/

section Value

variable (z : E → Bool)

/-- At a ternary vertex the affine expansion produced by the gadget is exactly the flow
factor. -/
theorem tern_eq_flowFactor (j : G.TernIdx) :
    (1 + (boolVal (z (ternA (F := F) G j)) : MvPolynomial ι F)
        + boolVal (z (ternB (F := F) G j)) + boolVal (z (ternC (F := F) G j)))
      = algebraMap F (MvPolynomial ι F) (flowFactor F G z j.1) := by
  obtain ⟨hs, ht, -⟩ := G.mem_ternVerts.mp j.2
  have hsum := (ternTripleOf_spec (F := F) G j).1 fun e => (boolVal (z e) : F)
  rw [flowFactor, if_neg hs, if_neg ht, hsum]
  simp only [map_add, map_one, algebraMap_boolVal]
  rw [ternA, ternB, ternC]
  ring

/-- The product of the affine flow factors kept by the support-two compiler. -/
theorem prod_flowForms2 :
    ((flowForms2 (ι := ι) (F := F) G).map fun Af => Af.eval (substSel (F := F) z)).prod
      = algebraMap F (MvPolynomial ι F)
          (∏ v ∈ Finset.univ.filter fun v => v ∉ G.ternVerts, flowFactor F G z v) := by
  rw [flowForms2, List.map_map, Finset.prod_map_toList, map_prod, Finset.prod_filter]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ G.ternVerts
  · simp only [Function.comp_apply, hv, if_pos]
    show AffineForm.eval (⟨1, []⟩ : AffineForm (ι ⊕ E) F) _ = 1
    simp [AffineForm.eval]
  · simp only [Function.comp_apply, if_neg hv, if_pos hv]
    exact eval_flowAff G z v

/-- The product over the ternary occurrences of the affine flow factors they produce. -/
theorem prod_ternIdx :
    (∏ j : G.TernIdx, (1 + (boolVal (z (ternA (F := F) G j)) : MvPolynomial ι F)
        + boolVal (z (ternB (F := F) G j)) + boolVal (z (ternC (F := F) G j))))
      = algebraMap F (MvPolynomial ι F)
          (∏ v ∈ Finset.univ.filter fun v => v ∈ G.ternVerts, flowFactor F G z v) := by
  rw [map_prod, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [← Finset.prod_coe_sort G.ternVerts
    (fun v => algebraMap F (MvPolynomial ι F) (flowFactor F G z v))]
  exact Finset.prod_congr rfl fun j _ => tern_eq_flowFactor G z j

/-- The full flow part: the kept affine factors together with the ternary expansions
reproduce the flow part of the selector polynomial. -/
theorem prod_flow_all :
    ((flowForms2 (ι := ι) (F := F) G).map fun Af => Af.eval (substSel (F := F) z)).prod
        * (∏ j : G.TernIdx, (1 + (boolVal (z (ternA (F := F) G j)) : MvPolynomial ι F)
            + boolVal (z (ternB (F := F) G j)) + boolVal (z (ternC (F := F) G j))))
      = algebraMap F (MvPolynomial ι F) (∏ v : V, flowFactor F G z v) := by
  rw [prod_flowForms2 G z, prod_ternIdx G z, ← map_mul]
  congr 1
  rw [mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => v ∈ G.ternVerts) _

/-- **The pointwise cubic-error killer, at a ternary vertex.**  For a fixed Boolean
selection `z`, the cubic error of the ternary gadget at `j` is annihilated by the
pair-exclusion factor of the two same-side edges of the triple. -/
theorem tern_error_kill (τ : F) (j : G.TernIdx) :
    (algebraMap F (MvPolynomial ι F) (kappaVal τ)⁻¹ *
        ((boolVal (z (ternA (F := F) G j)) : MvPolynomial ι F)
          * boolVal (z (ternB (F := F) G j)) * boolVal (z (ternC (F := F) G j))))
      * (∏ k : G.GadgetIdx, (1 + (gadgetX G lab k).eval (substSel (F := F) z)
          * (gadgetY (F := F) G k).eval (substSel (F := F) z))) = 0 := by
  have h2 : (2 : MvPolynomial ι F) = 0 := two_eq_zero_of_algebra F
  have hzero := boolVal_mul_mul_one_add_mul (R := MvPolynomial ι F) h2
    (z (ternA (F := F) G j)) (z (ternB (F := F) G j)) (z (ternC (F := F) G j))
  have hfinish : ∀ (k₀ : G.GadgetIdx),
      (1 + (gadgetX G lab k₀).eval (substSel (F := F) z)
        * (gadgetY (F := F) G k₀).eval (substSel (F := F) z))
        = 1 + (boolVal (z (ternA (F := F) G j)) : MvPolynomial ι F)
            * boolVal (z (ternB (F := F) G j)) →
      (algebraMap F (MvPolynomial ι F) (kappaVal τ)⁻¹ *
          ((boolVal (z (ternA (F := F) G j)) : MvPolynomial ι F)
            * boolVal (z (ternB (F := F) G j)) * boolVal (z (ternC (F := F) G j))))
        * (∏ k : G.GadgetIdx, (1 + (gadgetX G lab k).eval (substSel (F := F) z)
            * (gadgetY (F := F) G k).eval (substSel (F := F) z))) = 0 := by
    intro k₀ hk₀
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀), hk₀]
    set A := (boolVal (z (ternA (F := F) G j)) : MvPolynomial ι F)
    set B := (boolVal (z (ternB (F := F) G j)) : MvPolynomial ι F)
    set C := (boolVal (z (ternC (F := F) G j)) : MvPolynomial ι F)
    set R := ∏ k ∈ Finset.univ.erase k₀, (1 + (gadgetX G lab k).eval (substSel (F := F) z)
      * (gadgetY (F := F) G k).eval (substSel (F := F) z)) with hR
    calc algebraMap F (MvPolynomial ι F) (kappaVal τ)⁻¹ * (A * B * C) * ((1 + A * B) * R)
        = (A * B * C * (1 + A * B)) * (algebraMap F (MvPolynomial ι F) (kappaVal τ)⁻¹ * R) := by
          ring
      _ = 0 := by rw [hzero, zero_mul]
  rcases (ternTripleOf_spec (F := F) G j).2 with hp | hp
  · refine hfinish (Sum.inr (Sum.inl ⟨⟨j.1, (ternA (F := F) G j, ternB (F := F) G j)⟩, hp⟩)) ?_
    exact gadget_eval_inr_inl G lab z _
  · refine hfinish (Sum.inr (Sum.inr ⟨⟨j.1, (ternA (F := F) G j, ternB (F := F) G j)⟩, hp⟩)) ?_
    exact gadget_eval_inr_inr G lab z _

end Value

/-- **The support-two DAG compiler theorem.**  For a labelled DAG whose edge labels are
affine forms, the support-two compiled representation computes exactly the graph
polynomial `val G ℓ`. -/
theorem graphRep2_value {τ : F} (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1) :
    (graphRep2 G lab τ).value = val G (labelPoly lab) := by
  rw [graphRep2, compiled2_value τ (flowForms2 G) (ternA (F := F) G) (ternB (F := F) G)
    (ternC (F := F) G) (gadgetX G lab) (gadgetY G) hτ0 hτ1
    (fun z j => tern_error_kill G lab z τ j),
    ← abp_identity (M := MvPolynomial ι F) G F (labelPoly lab)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [prod_flow_all G z, prod_gadgetBodies G lab z, selectorVal, map_mul]
  ring

/-! ## Support, and size accounting -/

/-- Every affine flow factor kept by the support-two compiler mentions at most two
variables. -/
theorem flowForms2_numVars_le_two
    (hdeg : ∀ v : V, (G.inEdges v).card + (G.outEdges v).card ≤ 3)
    (hsrc : (G.outEdges G.s).card ≤ 2) (hsink : (G.inEdges G.t).card ≤ 2) :
    ∀ Af ∈ flowForms2 (ι := ι) (F := F) G, Af.numVars ≤ 2 := by
  intro Af hAf
  obtain ⟨v, -, rfl⟩ : ∃ v ∈ (Finset.univ : Finset V).toList,
      (if v ∈ G.ternVerts then (⟨1, []⟩ : AffineForm (ι ⊕ E) F) else flowAff G v) = Af := by
    simpa [flowForms2] using hAf
  by_cases hv : v ∈ G.ternVerts
  · simp [hv, numVars]
  · rw [if_neg hv, numVars_flowAff]
    have hdv := hdeg v
    rw [G.mem_ternVerts] at hv
    push_neg at hv
    split_ifs with h1 h2
    · exact h1 ▸ hsrc
    · exact h2 ▸ hsink
    · have := hv h1 h2
      omega

/-- **(SUPPORT2)** for a bounded-degree DAG with single-variable edge labels: every affine
factor of the support-two compiled representation mentions at most **two** variables. -/
theorem graphRep2_supportLE_two (τ : F)
    (hdeg : ∀ v : V, (G.inEdges v).card + (G.outEdges v).card ≤ 3)
    (hsrc : (G.outEdges G.s).card ≤ 2) (hsink : (G.inEdges G.t).card ≤ 2)
    (hlab : ∀ a : E, (lab a).numVars ≤ 1) :
    (graphRep2 G lab τ).SupportLE 2 :=
  compiled2.supportLE_two τ _ _ _ _ _ _
    (flowForms2_numVars_le_two G hdeg hsrc hsink)
    (numVars_gadgetX_le_one G lab hlab) (numVars_gadgetY_le_one G)

omit [CharP F 2] in
/-- **Size accounting, summed Boolean variables:** `q = 2|E| + D + P`, where `D` is the
number of internal vertices of total degree three. -/
theorem graphRep2_numAux (τ : F) :
    (graphRep2 G lab τ).numAux
      = Fintype.card E + G.ternVerts.card + (Fintype.card E + G.numPairs) := by
  rw [graphRep2, compiled2.numAux_eq, card_gadgetIdx, card_ternIdx]

omit [CharP F 2] in
/-- **Size accounting, affine factors:** `M = |V| + 4 D + 3(|E| + P)`. -/
theorem graphRep2_numFactors (τ : F) :
    (graphRep2 G lab τ).numFactors
      = Fintype.card V + 4 * G.ternVerts.card + 3 * (Fintype.card E + G.numPairs) := by
  rw [graphRep2, compiled2.numFactors_eq, length_flowForms2, card_gadgetIdx, card_ternIdx]

end PathGraph

end VNP1Char2
