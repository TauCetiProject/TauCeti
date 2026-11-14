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
* `TauCeti.toMeromorphicNFOn_conj_conj`: reflection commutes with normalization on a set.
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

/-- Reflection preserves whole-plane meromorphy in both directions. -/
@[simp]
theorem TauCeti.meromorphic_conj_conj_iff :
    Meromorphic (conj ∘ f ∘ conj) ↔ Meromorphic f :=
  ⟨fun hf ↦ by simpa [Function.comp_def] using hf.conj_conj, Meromorphic.conj_conj⟩

/-- Reflection preserves meromorphy on a set and reflects its domain. -/
@[simp]
theorem TauCeti.meromorphicOn_conj_conj_iff {U : Set ℂ} :
    MeromorphicOn (conj ∘ f ∘ conj) U ↔ MeromorphicOn f (conj ⁻¹' U) := by
  constructor <;> intro h z hz
  · simpa only [meromorphicAt_conj_conj_iff, Complex.conj_conj] using h (conj z) hz
  · exact meromorphicAt_conj_conj_iff.mpr
      (h (conj z) (by simpa only [Set.mem_preimage, Complex.conj_conj] using hz))

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

/-- Reflection across the real axis preserves meromorphic normal form. -/
theorem MeromorphicNFAt.conj_conj (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt (conj ∘ f ∘ conj) (conj x) := by
  rw [meromorphicNFAt_iff_analyticAt_or] at hf ⊢
  rcases hf with ha | ⟨hm, ho, hz⟩
  · exact Or.inl ha.conj_conj
  · exact Or.inr ⟨hm.conj_conj, by simpa using ho, by simp [Function.comp_def, hz]⟩

/-- Reflection preserves meromorphic normal form at the reflected point. -/
@[simp]
theorem TauCeti.meromorphicNFAt_conj_conj_iff :
    MeromorphicNFAt (conj ∘ f ∘ conj) x ↔ MeromorphicNFAt f (conj x) :=
  ⟨fun hf ↦ by simpa [Function.comp_def] using hf.conj_conj, fun hf ↦ by
    simpa using hf.conj_conj⟩

/-- Reflection preserves meromorphic normal form on a set and reflects its domain. -/
@[simp]
theorem TauCeti.meromorphicNFOn_conj_conj_iff {U : Set ℂ} :
    MeromorphicNFOn (conj ∘ f ∘ conj) U ↔ MeromorphicNFOn f (conj ⁻¹' U) := by
  constructor <;> intro h z hz
  · simpa only [meromorphicNFAt_conj_conj_iff, Complex.conj_conj] using h hz
  · exact meromorphicNFAt_conj_conj_iff.mpr
      (h (by simpa only [Set.mem_preimage, Complex.conj_conj] using hz))

/-- Normalizing a meromorphic germ commutes with reflection across the real axis. -/
@[simp]
theorem TauCeti.toMeromorphicNFAt_conj_conj (f : ℂ → ℂ) (x : ℂ) :
    toMeromorphicNFAt (conj ∘ f ∘ conj) x =
      conj ∘ toMeromorphicNFAt f (conj x) ∘ conj := by
  funext y
  by_cases hf : MeromorphicAt f (conj x)
  · by_cases hy : y = x
    · subst y
      have hc : Tendsto conj (𝓝[≠] x) (𝓝[≠] (conj x)) :=
        Complex.continuous_conj.continuousWithinAt.tendsto_nhdsWithin fun z hz ↦
          (starRingEnd ℂ).injective.ne hz
      have hn : MeromorphicNFAt (conj ∘ toMeromorphicNFAt f (conj x) ∘ conj) x := by
        simpa only [Complex.conj_conj] using
          (meromorphicNFAt_toMeromorphicNFAt (f := f) (x := conj x)).conj_conj
      apply (meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hn).mp _
        |>.eq_of_nhds
      filter_upwards [(meromorphicAt_conj_conj_iff.mpr hf).eq_nhdsNE_toMeromorphicNFAt,
        hc.eventually hf.eq_nhdsNE_toMeromorphicNFAt] with z hz hz'
      simp only [Function.comp_apply] at hz ⊢
      rw [← hz, ← hz']
    · simp only [Function.comp_apply]
      rw [← (meromorphicAt_conj_conj_iff.mpr hf).eqOn_compl_singleton_toMeromorphicNFAt
          (by simpa using hy),
        ← hf.eqOn_compl_singleton_toMeromorphicNFAt
          (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff,
            (starRingEnd ℂ).injective.eq_iff] using hy)]
      rfl
  · rw [toMeromorphicNFAt_of_not_meromorphicAt hf,
      toMeromorphicNFAt_of_not_meromorphicAt (meromorphicAt_conj_conj_iff.not.mpr hf)]
    simp

/-- Normalizing on a set commutes with reflection, including the zero fallback when the
function is not meromorphic on that set. -/
@[simp]
theorem TauCeti.toMeromorphicNFOn_conj_conj (f : ℂ → ℂ) (U : Set ℂ) :
    toMeromorphicNFOn (conj ∘ f ∘ conj) U =
      conj ∘ toMeromorphicNFOn f (conj ⁻¹' U) ∘ conj := by
  funext x
  simp only [Function.comp_apply]
  by_cases hf : MeromorphicOn f (conj ⁻¹' U)
  · have hm := meromorphicOn_conj_conj_iff.mpr hf
    by_cases hx : x ∈ U
    · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm hx,
        toMeromorphicNFOn_eq_toMeromorphicNFAt hf
          (by simpa only [Set.mem_preimage, Complex.conj_conj] using hx),
        toMeromorphicNFAt_conj_conj]
      rfl
    · rw [toMeromorphicNFOn_eq_self_on_compl hm hx,
        toMeromorphicNFOn_eq_self_on_compl hf
          (by simpa only [Set.mem_compl_iff, Set.mem_preimage, Complex.conj_conj] using hx)]
      rfl
  · simp only [toMeromorphicNFOn_of_not_meromorphicOn hf,
      toMeromorphicNFOn_of_not_meromorphicOn (meromorphicOn_conj_conj_iff.not.mpr hf),
      Pi.zero_apply, map_zero]
