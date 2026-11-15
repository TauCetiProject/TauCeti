/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Reflecting a function across the real axis

For `f : ℂ → ℂ`, the reflected function `conj ∘ f ∘ conj` is again holomorphic, meromorphic, in
meromorphic normal form, and has the same order, at the reflected point. Mathlib records the
differentiable case as `DifferentiableAt.conj_conj`; this file supplies the analytic, meromorphic,
and normal-form versions together with the invariance of `meromorphicOrderAt` and
`toMeromorphicNFAt`.

These are the statements needed to transport the analytic properties of a completed L-function and
its continued L-function to its dual, whose completed function is the reflection of the original
one.

## Main results

* `AnalyticAt.conj_conj`, `TauCeti.analyticAt_conj_conj_iff`: reflection preserves analyticity.
* `MeromorphicAt.conj_conj`, `TauCeti.meromorphicAt_conj_conj_iff`, `Meromorphic.conj_conj`:
  reflection preserves meromorphy.
* `TauCeti.meromorphicOrderAt_conj_conj`: reflection preserves the order of a meromorphic
  function.
* `MeromorphicNFAt.conj_conj`, `TauCeti.meromorphicNFAt_conj_conj_iff`,
  `TauCeti.toMeromorphicNFAt_conj_conj`: reflection preserves meromorphic normal form and commutes
  with conversion to normal form.
-/

public section

open ComplexConjugate Filter Topology

variable {f : ℂ → ℂ} {x : ℂ}

/-- If `f` is analytic at `x`, then `conj ∘ f ∘ conj` is analytic at `conj x`. This is the
one-variable case of `AnalyticAt.star_star`. -/
theorem AnalyticAt.conj_conj (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (conj ∘ f ∘ conj) (conj x) := by
  simpa only [Complex.star_def] using hf.star_star

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

/-- A function `f` is in meromorphic normal form at `conj x` iff `conj ∘ f ∘ conj` is in
meromorphic normal form at `x`. -/
@[simp]
theorem TauCeti.meromorphicNFAt_conj_conj_iff :
    MeromorphicNFAt (conj ∘ f ∘ conj) x ↔ MeromorphicNFAt f (conj x) := by
  simp [meromorphicNFAt_iff_analyticAt_or]

/-- If `f` is in meromorphic normal form at `x`, then `conj ∘ f ∘ conj` is in meromorphic normal
form at `conj x`. -/
theorem MeromorphicNFAt.conj_conj (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt (conj ∘ f ∘ conj) (conj x) := by
  simpa using hf

/-- Conversion to meromorphic normal form commutes with reflection across the real axis. -/
theorem TauCeti.toMeromorphicNFAt_conj_conj (f : ℂ → ℂ) (x : ℂ) :
    toMeromorphicNFAt (conj ∘ f ∘ conj) x = conj ∘ toMeromorphicNFAt f (conj x) ∘ conj := by
  by_cases hf : MeromorphicAt f (conj x)
  swap
  · rw [toMeromorphicNFAt_of_not_meromorphicAt hf,
      toMeromorphicNFAt_of_not_meromorphicAt (meromorphicAt_conj_conj_iff.not.2 hf)]
    ext z
    simp
  have hf' : MeromorphicAt (conj ∘ f ∘ conj) x := meromorphicAt_conj_conj_iff.2 hf
  have hne : ∀ z ≠ x, toMeromorphicNFAt (conj ∘ f ∘ conj) x z =
      (conj ∘ toMeromorphicNFAt f (conj x) ∘ conj) z := by
    intro z hz
    have hcz : conj z ≠ conj x := (starRingEnd ℂ).injective.ne hz
    simp only [Function.comp_apply, ← hf'.eqOn_compl_singleton_toMeromorphicNFAt hz,
      ← hf.eqOn_compl_singleton_toMeromorphicNFAt hcz]
  have hnhds : toMeromorphicNFAt (conj ∘ f ∘ conj) x =ᶠ[𝓝 x]
      conj ∘ toMeromorphicNFAt f (conj x) ∘ conj :=
    (meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (meromorphicNFAt_conj_conj_iff.2 meromorphicNFAt_toMeromorphicNFAt)).1
      (eventually_nhdsWithin_of_forall hne)
  ext z
  by_cases hz : z = x
  · subst z
    exact hnhds.eq_of_nhds
  · exact hne z hz

/-- Pointwise form of `TauCeti.toMeromorphicNFAt_conj_conj`. -/
@[simp]
theorem TauCeti.toMeromorphicNFAt_conj_conj_apply (f : ℂ → ℂ) (x z : ℂ) :
    toMeromorphicNFAt (conj ∘ f ∘ conj) x z = conj (toMeromorphicNFAt f (conj x) (conj z)) :=
  congrFun (TauCeti.toMeromorphicNFAt_conj_conj f x) z

