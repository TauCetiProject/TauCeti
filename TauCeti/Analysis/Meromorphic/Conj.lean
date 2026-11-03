/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order

/-!
# Reflecting a function across the real axis

For `f : ℂ → ℂ`, the reflected function `conj ∘ f ∘ conj` is again holomorphic, meromorphic, and
has the same order, at the reflected point. Mathlib records the differentiable case as
`DifferentiableAt.conj_conj`; this file supplies the analytic and meromorphic versions together
with the invariance of `meromorphicOrderAt`.

These are the statements needed to transport the analytic properties of a completed L-function to
its dual, whose completed function is the reflection of the original one.

## Main results

* `AnalyticAt.conj_conj`, `TauCeti.analyticAt_conj_conj_iff`: reflection preserves analyticity.
* `MeromorphicAt.conj_conj`, `TauCeti.meromorphicAt_conj_conj_iff`, `Meromorphic.conj_conj`:
  reflection preserves meromorphy.
* `TauCeti.meromorphicOrderAt_conj_conj`: reflection preserves the order of a meromorphic
  function.
-/

public section

open ComplexConjugate Filter Topology

variable {f : ℂ → ℂ} {x : ℂ}

/-- If `f` is analytic at `x`, then `conj ∘ f ∘ conj` is analytic at `conj x`. -/
theorem AnalyticAt.conj_conj (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (conj ∘ f ∘ conj) (conj x) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have hconj : Tendsto conj (𝓝 (conj x)) (𝓝 x) :=
    Complex.continuous_conj.tendsto' _ _ (Complex.conj_conj x)
  filter_upwards [hconj.eventually hf] with z hz
  exact differentiableAt_conj_conj_iff.2 hz

/-- A function `f` is analytic at `conj x` iff `conj ∘ f ∘ conj` is analytic at `x`. -/
@[simp]
theorem TauCeti.analyticAt_conj_conj_iff :
    AnalyticAt ℂ (conj ∘ f ∘ conj) x ↔ AnalyticAt ℂ f (conj x) :=
  ⟨fun hf ↦ by simpa [Function.comp_def] using hf.conj_conj, fun hf ↦ by
    simpa using hf.conj_conj⟩

/-- If `f` is meromorphic at `x`, then `conj ∘ f ∘ conj` is meromorphic at `conj x`. -/
theorem MeromorphicAt.conj_conj (hf : MeromorphicAt f x) :
    MeromorphicAt (conj ∘ f ∘ conj) (conj x) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, hn.conj_conj.congr (Eventually.of_forall fun z ↦ ?_)⟩
  simp

/-- A function `f` is meromorphic at `conj x` iff `conj ∘ f ∘ conj` is meromorphic at `x`. -/
@[simp]
theorem TauCeti.meromorphicAt_conj_conj_iff :
    MeromorphicAt (conj ∘ f ∘ conj) x ↔ MeromorphicAt f (conj x) :=
  ⟨fun hf ↦ by simpa [Function.comp_def] using hf.conj_conj, fun hf ↦ by
    simpa using hf.conj_conj⟩

/-- If `f` is meromorphic on `ℂ`, then so is `conj ∘ f ∘ conj`. -/
theorem Meromorphic.conj_conj (hf : Meromorphic f) : Meromorphic (conj ∘ f ∘ conj) :=
  fun _ ↦ TauCeti.meromorphicAt_conj_conj_iff.2 (hf _)

/-- Reflection across the real axis preserves the order of a meromorphic function:
the order of `conj ∘ f ∘ conj` at `x` is the order of `f` at `conj x`. -/
@[simp]
theorem TauCeti.meromorphicOrderAt_conj_conj :
    meromorphicOrderAt (conj ∘ f ∘ conj) x = meromorphicOrderAt f (conj x) := by
  by_cases hf : MeromorphicAt f (conj x)
  swap
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf,
      meromorphicOrderAt_of_not_meromorphicAt (meromorphicAt_conj_conj_iff.not.2 hf)]
  -- Conjugation carries the punctured neighbourhoods of `x` to those of `conj x`.
  have hconj : Tendsto conj (𝓝[≠] x) (𝓝[≠] (conj x)) :=
    Complex.continuous_conj.continuousWithinAt.tendsto_nhdsWithin fun z hz ↦
      (starRingEnd ℂ).injective.ne hz
  cases h : meromorphicOrderAt f (conj x) with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at h ⊢
    filter_upwards [hconj.eventually h] with z hz
    simp [hz]
  | coe n =>
    obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h
    refine (meromorphicOrderAt_eq_int_iff (meromorphicAt_conj_conj_iff.2 hf)).2
      ⟨conj ∘ g ∘ conj, analyticAt_conj_conj_iff.2 hg, by simpa using hg0, ?_⟩
    filter_upwards [hconj.eventually hfg] with z hz
    simp [hz]
