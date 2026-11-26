/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Order
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.Order

/-!
# Zero-free half-planes

A function `f : ℂ → ℂ` is *zero-free right of* `σ : ℝ` when `meromorphicOrderAt f s ≤ 0` at every
`s` with `σ < re s`. A zero is a point of positive order, so poles are allowed and no value of `f`
is read: the predicate treats alike a function with a pole at `s` whatever value it is given at
`s`. This is the form in which the Riemann hypothesis of a Dirichlet L-function is stated,
`ZeroFreeRightOf (1 / 2)` of its meromorphic continuation: the pole at `1`, when there is one
(for the trivial character), is allowed.

Mathlib's order of a function that is not meromorphic at a point is the junk value `0`. So a
point where `f` is not meromorphic passes the test automatically, while a point where `f` is
meromorphic of positive order fails it; the predicate says what its name suggests for functions
meromorphic on the half-plane, and the product rules below assume as much meromorphy as they
need.

## Main definitions

* `TauCeti.ZeroFreeRightOf`: the predicate.

## Main results

* `TauCeti.zeroFreeRightOf_iff`: the pointwise order characterization, which unfolds the
  predicate.
* `TauCeti.ZeroFreeRightOf.mono`, `TauCeti.zeroFreeRightOf_iff_forall_gt`: monotonicity in `σ`,
  and the predicate at `σ` as the conjunction of the predicates at all `σ' > σ`.
* `TauCeti.zeroFreeRightOf_congr`: the predicate depends only on punctured germs.
* `TauCeti.zeroFreeRightOf_iff_of_analyticAt`: for a function analytic on the half-plane, the
  predicate says that no value there is `0`.
* `TauCeti.ZeroFreeRightOf.mul`, `TauCeti.zeroFreeRightOf_mul_iff`,
  `TauCeti.zeroFreeRightOf_mul_iff_of_meromorphicOrderAt_eq_zero`,
  `TauCeti.zeroFreeRightOf_mul_iff_of_ne_zero`: products.
* `TauCeti.zeroFreeRightOf_conj_conj_iff`, `TauCeti.zeroFreeRightOf_comp_add_const`: reflection in
  the real axis and translation.
* `TauCeti.not_zeroFreeRightOf_zero`: the zero function is zero-free right of no `σ`.

The pointwise statements about orders that these lift are in
`TauCeti.Analysis.Meromorphic.Order`.

## References

* OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane `Re(s) > 7/8`*, preprint of
  30 September 2026, Theorem 1.1 and section 2, for the convention that a zero-free half-plane
  is a statement about the meromorphic continuation in which poles are allowed.
-/

public section

open Filter Topology
open scoped ComplexConjugate

namespace TauCeti

/-- `f` is zero-free right of `σ`: at every `s` with `σ < re s` the order of `f` is at most `0`.
Poles are allowed, and no value of `f` is read. A point where `f` is not meromorphic passes the
test, since Mathlib's order is then the junk value `0`; a point where `f` is meromorphic of
positive order fails it. -/
def ZeroFreeRightOf (σ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s ≤ 0

variable {σ σ' : ℝ} {f g : ℂ → ℂ}

/-- The pointwise order characterization of `ZeroFreeRightOf`, used to unfold the predicate: `f`
is zero-free right of `σ` exactly when its order is at most `0` at every `s` with `σ < re s`. -/
theorem zeroFreeRightOf_iff :
    ZeroFreeRightOf σ f ↔ ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s ≤ 0 :=
  Iff.rfl

/-- A function zero-free right of `σ` is zero-free right of every `σ' ≥ σ`. -/
theorem ZeroFreeRightOf.mono (h : ZeroFreeRightOf σ f) (hσ : σ ≤ σ') : ZeroFreeRightOf σ' f :=
  fun s hs => h s (hσ.trans_lt hs)

/-- `f` is zero-free right of `σ` exactly when it is zero-free right of every `σ' > σ`. -/
theorem zeroFreeRightOf_iff_forall_gt :
    ZeroFreeRightOf σ f ↔ ∀ σ' > σ, ZeroFreeRightOf σ' f := by
  refine ⟨fun h σ' hσ' => h.mono hσ'.le, fun h s hs => ?_⟩
  obtain ⟨σ', hσ, hσ'⟩ := exists_between hs
  exact h σ' hσ s hσ'

/-- The predicate depends only on punctured germs: two functions that agree on a punctured
neighbourhood of every point right of `σ` are zero-free right of `σ` together. This lifts
`meromorphicOrderAt_congr`. -/
theorem zeroFreeRightOf_congr (h : ∀ s : ℂ, σ < s.re → f =ᶠ[𝓝[≠] s] g) :
    ZeroFreeRightOf σ f ↔ ZeroFreeRightOf σ g :=
  forall₂_congr fun s hs => by rw [meromorphicOrderAt_congr (h s hs)]

/-- A function analytic at every point right of `σ` is zero-free right of `σ` exactly when it
has no zero there. This lifts `AnalyticAt.meromorphicOrderAt_nonpos_iff`. -/
theorem zeroFreeRightOf_iff_of_analyticAt (hf : ∀ s : ℂ, σ < s.re → AnalyticAt ℂ f s) :
    ZeroFreeRightOf σ f ↔ ∀ s : ℂ, σ < s.re → f s ≠ 0 :=
  forall₂_congr fun s hs => (hf s hs).meromorphicOrderAt_nonpos_iff

/-- The zero function is zero-free right of no `σ`: its order is `⊤` everywhere. -/
@[simp]
theorem not_zeroFreeRightOf_zero (σ : ℝ) : ¬ZeroFreeRightOf σ 0 := fun h => by
  have h0 : meromorphicOrderAt (0 : ℂ → ℂ) ((σ + 1 : ℝ) : ℂ) = ⊤ := by
    simp
  have := h ((σ + 1 : ℝ) : ℂ) (by simp)
  rw [h0] at this
  exact WithTop.zero_ne_top (top_le_iff.1 this)

/-- The product of two functions zero-free right of `σ`, one of which is meromorphic at every
point right of `σ`, is zero-free right of `σ`. At a point where the other factor is not
meromorphic the product is not meromorphic either, and its order is the junk value `0`. One
meromorphy hypothesis is needed: `(s - 2) * exp (conj s)` and `exp (-conj s)` are meromorphic at
no point, so both are zero-free right of every `σ`, while their product `s - 2` is not zero-free
right of `1`. This lifts `MeromorphicAt.meromorphicOrderAt_mul_nonpos`. -/
theorem ZeroFreeRightOf.mul (hf : ZeroFreeRightOf σ f) (hg : ZeroFreeRightOf σ g)
    (hfm : ∀ s : ℂ, σ < s.re → MeromorphicAt f s) : ZeroFreeRightOf σ (f * g) :=
  fun s hs => (hfm s hs).meromorphicOrderAt_mul_nonpos (hf s hs) (hg s hs)

/-- Let `f` and `g` be meromorphic at every point right of `σ`, such that no pole of either
there is a zero of the other. Then `f * g` is zero-free right of `σ` exactly when `f` and `g`
both are. The conditions at the poles are needed: `(s - 1)⁻¹ * (s - 1)` is zero-free right of
every `σ`. This lifts `MeromorphicAt.meromorphicOrderAt_mul_nonpos_iff`. -/
theorem zeroFreeRightOf_mul_iff (hfm : ∀ s : ℂ, σ < s.re → MeromorphicAt f s)
    (hgm : ∀ s : ℂ, σ < s.re → MeromorphicAt g s)
    (hfg : ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt g s ≤ 0)
    (hgf : ∀ s : ℂ, σ < s.re → meromorphicOrderAt g s < 0 → meromorphicOrderAt f s ≤ 0) :
    ZeroFreeRightOf σ (f * g) ↔ ZeroFreeRightOf σ f ∧ ZeroFreeRightOf σ g := by
  have key := fun (s : ℂ) (hs : σ < s.re) =>
    (hfm s hs).meromorphicOrderAt_mul_nonpos_iff (hgm s hs) (hfg s hs) (hgf s hs)
  exact ⟨fun h => ⟨fun s hs => ((key s hs).1 (h s hs)).1, fun s hs => ((key s hs).1 (h s hs)).2⟩,
    fun h => h.1.mul h.2 hfm⟩

/-- Multiplying by a function that is meromorphic of order `0` at every point right of `σ` does
not change whether a function is zero-free right of `σ`. No meromorphy of the other factor is
assumed and no value of `g` is read. This lifts
`MeromorphicAt.meromorphicOrderAt_mul_of_meromorphicOrderAt_eq_zero`. -/
theorem zeroFreeRightOf_mul_iff_of_meromorphicOrderAt_eq_zero
    (hgm : ∀ s : ℂ, σ < s.re → MeromorphicAt g s)
    (hg0 : ∀ s : ℂ, σ < s.re → meromorphicOrderAt g s = 0) :
    ZeroFreeRightOf σ (f * g) ↔ ZeroFreeRightOf σ f :=
  forall₂_congr fun s hs => by
    rw [mul_comm, (hgm s hs).meromorphicOrderAt_mul_of_meromorphicOrderAt_eq_zero (hg0 s hs)]

/-- Multiplying by a function analytic and nonzero at every point right of `σ` does not change
whether a function is zero-free right of `σ`: the half-plane form of Mathlib's
`meromorphicOrderAt_mul_of_ne_zero`. -/
theorem zeroFreeRightOf_mul_iff_of_ne_zero (hg : ∀ s : ℂ, σ < s.re → AnalyticAt ℂ g s)
    (hg0 : ∀ s : ℂ, σ < s.re → g s ≠ 0) :
    ZeroFreeRightOf σ (f * g) ↔ ZeroFreeRightOf σ f :=
  zeroFreeRightOf_mul_iff_of_meromorphicOrderAt_eq_zero (fun s hs => (hg s hs).meromorphicAt)
    fun s hs => le_antisymm ((hg s hs).meromorphicOrderAt_nonpos_iff.2 (hg0 s hs))
      (hg s hs).meromorphicOrderAt_nonneg

/-- Reflection in the real axis: `conj ∘ f ∘ conj` is zero-free right of `σ` exactly when `f`
is. No meromorphy is assumed. This lifts `meromorphicOrderAt_conj_conj`. -/
@[simp]
theorem zeroFreeRightOf_conj_conj_iff :
    ZeroFreeRightOf σ (conj ∘ f ∘ conj) ↔ ZeroFreeRightOf σ f := by
  have hinv : Function.Involutive (conj : ℂ → ℂ) := Complex.conj_conj
  exact (hinv.toPerm conj).forall_congr fun s => by
    rw [hinv.coe_toPerm, meromorphicOrderAt_conj_conj, Complex.conj_re]

/-- Translation: `s ↦ f (s + a)` is zero-free right of `σ` exactly when `f` is zero-free right of
`σ + re a`. This lifts Mathlib's
`meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt`. -/
theorem zeroFreeRightOf_comp_add_const (a : ℂ) :
    ZeroFreeRightOf σ (fun s => f (s + a)) ↔ ZeroFreeRightOf (σ + a.re) f :=
  (Equiv.addRight a).forall_congr fun s => by
    rw [Equiv.coe_addRight, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt,
      Complex.add_re, add_lt_add_iff_right]

end TauCeti
