/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Divisor
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Reflecting a function across the real axis

For `f : ℂ → ℂ`, the reflected function `conj ∘ f ∘ conj` is again holomorphic, meromorphic, and
has the same order, at the reflected point. Mathlib records the differentiable case as
`DifferentiableAt.conj_conj`; this file supplies the analytic and meromorphic versions together
with the invariance of `meromorphicOrderAt` and `MeromorphicOn.divisor`.

These are the statements needed to transport the analytic properties of a completed L-function to
its dual, whose completed function is the reflection of the original one.

## Main results

* `AnalyticAt.conj_conj`, `TauCeti.analyticAt_conj_conj_iff`: reflection preserves analyticity.
* `MeromorphicAt.conj_conj`, `TauCeti.meromorphicAt_conj_conj_iff`, `Meromorphic.conj_conj`:
  reflection preserves meromorphy.
* `TauCeti.meromorphicOrderAt_conj_conj`: reflection preserves the order of a meromorphic
  function.
* `TauCeti.meromorphicOrderAt_sub_conj_of_ne_zero`, `TauCeti.meromorphicOrderAt_sub_conj`,
  `TauCeti.divisor_sub_conj`: under punctured-neighbourhood functional-conjugation symmetry
  `f (a - w) = c * conj (f (conj w))`, `z ↦ a - conj z` preserves `meromorphicOrderAt f` and
  `MeromorphicOn.divisor f U`.
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

/-- Under a punctured-neighbourhood functional-conjugation identity at `conj z` with a nonzero
multiplier `c ≠ 0`, the reflection `z ↦ a - conj z` preserves `meromorphicOrderAt f`. -/
theorem TauCeti.meromorphicOrderAt_sub_conj_of_ne_zero {f : ℂ → ℂ} {a c z : ℂ}
    (hfe : (fun w ↦ f (a - w)) =ᶠ[𝓝[≠] (conj z)] fun w ↦ c * conj (f (conj w))) (hc : c ≠ 0) :
    meromorphicOrderAt f (a - conj z) = meromorphicOrderAt f z := by
  have hlhs : meromorphicOrderAt (fun w : ℂ ↦ f (a - w)) (conj z) =
      meromorphicOrderAt f (a - conj z) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (g := fun w : ℂ ↦ a - w)
      (by fun_prop) (by simp)
  have hrhs : meromorphicOrderAt (fun w : ℂ ↦ c * conj (f (conj w))) (conj z) =
      meromorphicOrderAt f z := by
    have hsmul : (fun w : ℂ ↦ c * conj (f (conj w))) = c • (conj ∘ f ∘ conj) := by
      funext w
      simp [Function.comp_def, smul_eq_mul]
    rw [hsmul, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc,
      meromorphicOrderAt_conj_conj, Complex.conj_conj]
  rw [← hlhs, meromorphicOrderAt_congr hfe, hrhs]

/-- Under punctured-neighbourhood functional-conjugation identities at `conj z` and `a - z`
(including the degenerate case `c = 0`), the reflection `z ↦ a - conj z` preserves
`meromorphicOrderAt f`. -/
theorem TauCeti.meromorphicOrderAt_sub_conj {f : ℂ → ℂ} {a c z : ℂ}
    (hfe : (fun w ↦ f (a - w)) =ᶠ[𝓝[≠] (conj z)] fun w ↦ c * conj (f (conj w)))
    (hfe' : (fun w ↦ f (a - w)) =ᶠ[𝓝[≠] (a - z)] fun w ↦ c * conj (f (conj w))) :
    meromorphicOrderAt f (a - conj z) = meromorphicOrderAt f z := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hsub (u : ℂ) : Tendsto (fun v : ℂ ↦ a - v) (𝓝[≠] u) (𝓝[≠] (a - u)) :=
      (continuous_const.sub continuous_id).continuousWithinAt.tendsto_nhdsWithin fun v hv ↦
        sub_right_injective.ne hv
    have h1 : ∀ᶠ v in 𝓝[≠] (a - conj z), f v = 0 := by
      have ht := hsub (a - conj z)
      rw [sub_sub_cancel] at ht
      filter_upwards [ht.eventually hfe] with v hv
      simpa using hv
    have h2 : ∀ᶠ v in 𝓝[≠] z, f v = 0 := by
      filter_upwards [(hsub z).eventually hfe'] with v hv
      simpa using hv
    rw [meromorphicOrderAt_eq_top_iff.mpr h1, meromorphicOrderAt_eq_top_iff.mpr h2]
  · exact meromorphicOrderAt_sub_conj_of_ne_zero hfe hc

/-- Under punctured-neighbourhood functional-conjugation identities at `conj z` and `a - z`
(including the degenerate case `c = 0`), if `a - conj z ∈ U ↔ z ∈ U`, then the reflection
`z ↦ a - conj z` preserves `MeromorphicOn.divisor f U`. -/
theorem TauCeti.divisor_sub_conj {f : ℂ → ℂ} {U : Set ℂ} {a c z : ℂ}
    (hU : a - conj z ∈ U ↔ z ∈ U)
    (hfe : (fun w ↦ f (a - w)) =ᶠ[𝓝[≠] (conj z)] fun w ↦ c * conj (f (conj w)))
    (hfe' : (fun w ↦ f (a - w)) =ᶠ[𝓝[≠] (a - z)] fun w ↦ c * conj (f (conj w))) :
    MeromorphicOn.divisor f U (a - conj z) = MeromorphicOn.divisor f U z := by
  by_cases hm : MeromorphicOn f U
  · by_cases hz : z ∈ U
    · rw [hm.divisor_apply (hU.mpr hz), hm.divisor_apply hz,
        meromorphicOrderAt_sub_conj hfe hfe']
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (mt hU.mp hz),
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
  · simp [MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hm]
