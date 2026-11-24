/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Meromorphic.Conj

/-!
# Zero-free half-planes

A function `f : ℂ → ℂ` is *zero-free right of* `σ : ℝ` when `meromorphicOrderAt f s ≤ 0` at every
`s` with `σ < re s`. A zero is a point of positive order, so poles are allowed and no value of `f`
is read: the predicate treats alike a function with a pole at `s` whatever value it is given at
`s`. This is the form in which the Riemann hypothesis of an L-function is stated,
`ZeroFreeRightOf (1 / 2)` of its meromorphic continuation, the pole at `1` included.

Mathlib's order of a function that is not meromorphic at a point is the junk value `0`, so the
predicate carries information only for functions meromorphic on the half-plane, and the product
rules below assume as much meromorphy as they need.

## Main definitions

* `TauCeti.ZeroFreeRightOf`: the predicate.

## Main results

* `TauCeti.ZeroFreeRightOf.mono`, `TauCeti.zeroFreeRightOf_iff_forall_gt`: monotonicity in `σ`,
  and the predicate at `σ` as the conjunction of the predicates at all `σ' > σ`.
* `TauCeti.zeroFreeRightOf_congr`: the predicate depends only on punctured germs.
* `AnalyticAt.meromorphicOrderAt_le_zero_iff`, `TauCeti.zeroFreeRightOf_iff_of_analyticAt`: at a
  point of analyticity the order is at most `0` exactly when the value is nonzero.
* `TauCeti.ZeroFreeRightOf.mul`, `TauCeti.zeroFreeRightOf_mul_iff`,
  `TauCeti.zeroFreeRightOf_mul_iff_of_analyticAt`: products.
* `TauCeti.zeroFreeRightOf_conj_conj`, `TauCeti.zeroFreeRightOf_comp_add_const`: reflection in the
  real axis and translation.
* `TauCeti.not_zeroFreeRightOf_zero`: the zero function is zero-free right of no `σ`.
-/

public section

open Filter Topology
open scoped ComplexConjugate

/-- At a point where `f` is analytic, the order of `f` is at most `0` exactly when `f` does not
vanish there. -/
theorem AnalyticAt.meromorphicOrderAt_le_zero_iff {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    meromorphicOrderAt f x ≤ 0 ↔ f x ≠ 0 := by
  rw [← hf.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
  exact ⟨fun h => le_antisymm h hf.meromorphicOrderAt_nonneg, fun h => h.le⟩

namespace TauCeti

/-- `f` is zero-free right of `σ`: at every `s` with `σ < re s` the order of `f` is at most `0`.
Poles are allowed, and no value of `f` is read. -/
def ZeroFreeRightOf (σ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s ≤ 0

variable {σ σ' : ℝ} {f g : ℂ → ℂ}

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
neighbourhood of every point right of `σ` are zero-free right of `σ` together. -/
theorem zeroFreeRightOf_congr (h : ∀ s : ℂ, σ < s.re → f =ᶠ[𝓝[≠] s] g) :
    ZeroFreeRightOf σ f ↔ ZeroFreeRightOf σ g :=
  forall₂_congr fun s hs => by rw [meromorphicOrderAt_congr (h s hs)]

/-- A function analytic at every point right of `σ` is zero-free right of `σ` exactly when it
has no zero there. -/
theorem zeroFreeRightOf_iff_of_analyticAt (hf : ∀ s : ℂ, σ < s.re → AnalyticAt ℂ f s) :
    ZeroFreeRightOf σ f ↔ ∀ s : ℂ, σ < s.re → f s ≠ 0 :=
  forall₂_congr fun s hs => (hf s hs).meromorphicOrderAt_le_zero_iff

/-- The zero function is zero-free right of no `σ`: its order is `⊤` everywhere. -/
theorem not_zeroFreeRightOf_zero (σ : ℝ) : ¬ZeroFreeRightOf σ 0 := fun h => by
  have h0 : meromorphicOrderAt (0 : ℂ → ℂ) ((σ + 1 : ℝ) : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ => rfl)
  have := h ((σ + 1 : ℝ) : ℂ) (by simp)
  rw [h0] at this
  exact WithTop.zero_ne_top (top_le_iff.1 this)

/-- The product of two functions zero-free right of `σ`, one of which is meromorphic at every
point right of `σ`, is zero-free right of `σ`. At a point where the other factor is not
meromorphic the product is not meromorphic either, and its order is the junk value `0`. One
meromorphy hypothesis is needed: `(s - 2) * exp (conj s)` and `exp (-conj s)` are meromorphic at
no point, so both are zero-free right of every `σ`, while their product `s - 2` is not zero-free
right of `1`. -/
theorem ZeroFreeRightOf.mul (hf : ZeroFreeRightOf σ f) (hg : ZeroFreeRightOf σ g)
    (hfm : ∀ s : ℂ, σ < s.re → MeromorphicAt f s) : ZeroFreeRightOf σ (f * g) := fun s hs => by
  by_cases hgm : MeromorphicAt g s
  · rw [meromorphicOrderAt_mul (hfm s hs) hgm]
    exact add_nonpos (hf s hs) (hg s hs)
  · have hne : ∀ᶠ z in 𝓝[≠] s, f z ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hfm s hs)).1
        (ne_top_of_le_ne_top WithTop.zero_ne_top (hf s hs))
    have hfg : ¬MeromorphicAt (f * g) s := fun h => hgm <|
      (h.mul (hfm s hs).inv).congr <| hne.mono fun z hz => by
        rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, mul_right_comm, mul_inv_cancel₀ hz, one_mul]
    rw [meromorphicOrderAt_of_not_meromorphicAt hfg]

/-- Let `f` and `g` be meromorphic at every point right of `σ`, where `g` has no pole and every
pole of `f` is a point of order `0` of `g`. Then `f * g` is zero-free right of `σ` exactly when
`f` and `g` both are. The condition at the poles of `f` is needed: `(s - 1)⁻¹ * (s - 1)` is
zero-free right of every `σ`. -/
theorem zeroFreeRightOf_mul_iff (hfm : ∀ s : ℂ, σ < s.re → MeromorphicAt f s)
    (hgm : ∀ s : ℂ, σ < s.re → MeromorphicAt g s)
    (hg : ∀ s : ℂ, σ < s.re → 0 ≤ meromorphicOrderAt g s)
    (hfg : ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt g s = 0) :
    ZeroFreeRightOf σ (f * g) ↔ ZeroFreeRightOf σ f ∧ ZeroFreeRightOf σ g := by
  refine ⟨fun h => ?_, fun h => h.1.mul h.2 hfm⟩
  have key : ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s ≤ 0 ∧ meromorphicOrderAt g s ≤ 0 := by
    intro s hs
    have hmul := h s hs
    rw [meromorphicOrderAt_mul (hfm s hs) (hgm s hs)] at hmul
    rcases lt_or_ge (meromorphicOrderAt f s) 0 with hf | hf
    · exact ⟨hf.le, (hfg s hs hf).le⟩
    · exact ⟨(le_add_of_nonneg_right (hg s hs)).trans hmul,
        (le_add_of_nonneg_left hf).trans hmul⟩
  exact ⟨fun s hs => (key s hs).1, fun s hs => (key s hs).2⟩

/-- Multiplying by a function analytic and nonzero at every point right of `σ` does not change
whether a function is zero-free right of `σ`. -/
theorem zeroFreeRightOf_mul_iff_of_analyticAt (hg : ∀ s : ℂ, σ < s.re → AnalyticAt ℂ g s)
    (hg0 : ∀ s : ℂ, σ < s.re → g s ≠ 0) :
    ZeroFreeRightOf σ (f * g) ↔ ZeroFreeRightOf σ f :=
  forall₂_congr fun s hs => by
    rw [mul_comm, meromorphicOrderAt_mul_of_ne_zero (hg s hs) (hg0 s hs)]

/-- Reflection in the real axis: `conj ∘ f ∘ conj` is zero-free right of `σ` exactly when `f`
is. No meromorphy is assumed. -/
@[simp]
theorem zeroFreeRightOf_conj_conj :
    ZeroFreeRightOf σ (conj ∘ f ∘ conj) ↔ ZeroFreeRightOf σ f := by
  constructor
  · intro h s hs
    simpa using h (conj s) (by simpa using hs)
  · intro h s hs
    rw [meromorphicOrderAt_conj_conj]
    exact h _ (by simpa using hs)

/-- Translation: `s ↦ f (s + a)` is zero-free right of `σ` exactly when `f` is zero-free right of
`σ + re a`. -/
theorem zeroFreeRightOf_comp_add_const (a : ℂ) :
    ZeroFreeRightOf σ (fun s => f (s + a)) ↔ ZeroFreeRightOf (σ + a.re) f := by
  have key : ∀ s : ℂ, meromorphicOrderAt (fun s => f (s + a)) s = meromorphicOrderAt f (s + a) :=
    fun s => meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt
  constructor
  · intro h s hs
    have := h (s - a) (by rw [Complex.sub_re]; linarith)
    rwa [key, sub_add_cancel] at this
  · intro h s hs
    rw [key]
    exact h _ (by rw [Complex.add_re]; linarith)

end TauCeti
