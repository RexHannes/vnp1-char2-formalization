/-
# Formal nondeterminism closure

Mirroring BIZ Definition 2.2, the nondeterministic closure `N(C)` of a class `C` of
polynomial families consists of the families

```
f_n(x) = ∑_{b ∈ {0,1}^{p(n)}} g_{q(n)}(b, x)
```

with `p`, `q` polynomially bounded and `g ∈ C`.

Concretely, the `n`-th member of `f` has variables `Fin (f.nvars n)`, and the member
`g_{q(n)}` is a polynomial in `Fin (g.nvars (q n))` variables of which the first
`f.nvars n` are the original variables `x` and the remaining ones are the witness bits;
`witnessSubst` performs exactly this substitution.  The side condition
`g.nvars (q n) ≤ f.nvars n + p n` says that all the variables of `g_{q(n)}` really are
original variables or witness bits.

No literature theorem (in particular not Valiant's `VNP_e = VNP`) is imported here, as an
axiom or otherwise.
-/
import RequestProject.AlgebraicComplexity.VNP1Char2.PFamily

namespace VNP1Char2

open scoped BigOperators
open MvPolynomial

variable {F : Type} [Field F]

/-! ## The witness substitution -/

/-- Substituting the first `m` variables by themselves and the next `k` variables by the
Boolean witness bits `b`. -/
noncomputable def witnessSubst (m k : ℕ) {N : ℕ} (b : Fin k → Bool) :
    Fin N → MvPolynomial (Fin m) F := fun i =>
  if h : (i : ℕ) < m then X ⟨i, h⟩
  else if h₂ : (i : ℕ) - m < k then boolVal (b ⟨(i : ℕ) - m, h₂⟩) else 0

/-- The index-level version of `witnessSubst`: under `N ≤ m + k`, every variable of the
inner polynomial is either one of the `m` original variables or one of the `k` witness
bits. -/
def witnessIdx {m k N : ℕ} (h : N ≤ m + k) (i : Fin N) : Fin m ⊕ Fin k :=
  if hm : (i : ℕ) < m then Sum.inl ⟨i, hm⟩
  else Sum.inr ⟨(i : ℕ) - m, by have := i.2; omega⟩

theorem witnessSubst_eq_elim {m k N : ℕ} (h : N ≤ m + k) (b : Fin k → Bool) :
    (witnessSubst (F := F) m k (N := N) b)
      = fun i => Sum.elim (fun j => (X j : MvPolynomial (Fin m) F))
          (fun j => boolVal (b j)) (witnessIdx h i) := by
  funext i
  unfold witnessSubst witnessIdx
  by_cases hm : (i : ℕ) < m
  · simp [hm]
  · have hi := i.2
    have h₂ : (i : ℕ) - m < k := by omega
    simp [hm, h₂]

theorem witnessSubst_zero (m : ℕ) (b : Fin 0 → Bool) :
    (witnessSubst (F := F) m 0 (N := m) b) = fun i => (X i : MvPolynomial (Fin m) F) := by
  funext i
  have : (i : ℕ) < m := i.2
  simp [witnessSubst, this]

/-! ## The closure operator -/

/-- **Nondeterministic closure.**  `NondetClosure C f` holds when `f` is obtained from a
family `g ∈ C` by summing polynomially many Boolean witness bits. -/
def NondetClosure (C : PolyFamily F → Prop) (f : PolyFamily F) : Prop :=
  PolyBounded f.nvars ∧
    ∃ (g : PolyFamily F) (p q : ℕ → ℕ), C g ∧ PolyBounded p ∧ PolyBounded q ∧
      ∀ n, g.nvars (q n) ≤ f.nvars n + p n ∧
        f.poly n = ∑ b : Fin (p n) → Bool,
          aeval (witnessSubst (f.nvars n) (p n) b) (g.poly (q n))

/-- The nondeterministic closure of the formula class. -/
def VNPe (f : PolyFamily F) : Prop := NondetClosure VPe f

theorem NondetClosure.mono {C D : PolyFamily F → Prop} (h : ∀ g, C g → D g) {f : PolyFamily F}
    (hf : NondetClosure C f) : NondetClosure D f := by
  obtain ⟨hv, g, p, q, hg, hp, hq, hrep⟩ := hf
  exact ⟨hv, g, p, q, h g hg, hp, hq, hrep⟩

/-- A class with polynomially bounded variable counts is contained in its nondeterministic
closure: take no witness bits at all. -/
theorem subset_nondetClosure {C : PolyFamily F → Prop} {f : PolyFamily F} (hf : C f)
    (hv : PolyBounded f.nvars) : NondetClosure C f := by
  refine ⟨hv, f, (fun _ => 0), (fun n => n), hf, polyBounded_const 0, polyBounded_id,
    fun n => ⟨by simp, ?_⟩⟩
  rw [Fintype.sum_unique, witnessSubst_zero]
  simp

/-- `VP_e ⊆ VNP_e` (formula version of the nondeterministic closure). -/
theorem VPe.toVNPe {f : PolyFamily F} (hf : VPe f) : VNPe f :=
  subset_nondetClosure hf hf.1

end VNP1Char2
