/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Calculus.Deriv.Parity

/-!
# Symmetries of logarithmic derivatives under affine reflection and conjugation

This file records the elementary behavior of `logDeriv f = deriv f / f` under reflection
`w ↦ a - w` (`TauCeti.logDeriv_comp_const_sub`), evenness at the origin
(`Function.Even.logDeriv_zero`), conjugation `conj ∘ f ∘ conj` (`TauCeti.logDeriv_conj_conj`),
and the combined affine-conjugation reflection `f (a - conj w) = u * conj (f w)`
(`TauCeti.logDeriv_sub_conj_nhds_of_ne_zero`, `TauCeti.logDeriv_sub_conj_nhds`,
`TauCeti.logDeriv_sub_conj`). None of these identities require differentiability of `f` (where `f`
is not differentiable, both `deriv` and `logDeriv` vanish under Lean's totalized convention).

## Main results

* `TauCeti.logDeriv_comp_const_sub`: `logDeriv (fun w ↦ f (a - w)) x = -logDeriv f (a - x)`.
* `Function.Even.logDeriv_zero`: `logDeriv f 0 = 0` for any even function `f` in characteristic `0`.
* `TauCeti.logDeriv_conj_conj`: `logDeriv (conj ∘ f ∘ conj) z = conj (logDeriv f (conj z))`.
* `TauCeti.logDeriv_sub_conj_nhds_of_ne_zero`, `TauCeti.logDeriv_sub_conj_nhds`,
  `TauCeti.logDeriv_sub_conj`: local germ and whole-space reflection identities
  `logDeriv f (a - conj z) = -conj (logDeriv f z)`.
-/

public section

open ComplexConjugate Filter Topology

/-- The logarithmic derivative of an even function vanishes at `0` over a field of characteristic
zero, with no differentiability or nonvanishing assumption. -/
theorem Function.Even.logDeriv_zero {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {f : 𝕜 → 𝕜'} (hf : f.Even) :
    logDeriv f 0 = 0 := by
  rw [logDeriv_apply, hf.deriv_zero, zero_div]

namespace TauCeti

/-- Reflection `w ↦ a - w` negates the logarithmic derivative, with no differentiability
assumption on `f`. -/
@[simp]
theorem logDeriv_comp_const_sub {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] (f : 𝕜 → 𝕜') (a x : 𝕜) :
    logDeriv (fun w ↦ f (a - w)) x = -logDeriv f (a - x) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_sub, neg_div]

/-- The logarithmic derivative of `conj ∘ f ∘ conj` at `z` is `conj (logDeriv f (conj z))`
(matching Mathlib's `deriv_conj_conj`), with no differentiability assumption on `f`. -/
@[simp]
theorem logDeriv_conj_conj {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
    [NormedStarGroup 𝕜] (f : 𝕜 → 𝕜) (z : 𝕜) :
    logDeriv (conj ∘ f ∘ conj) z = conj (logDeriv f (conj z)) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_conj_conj]
  simp

/-- **Local logarithmic-derivative symmetry under `w ↦ a - conj w`, for a nonzero multiplier.**
If `(fun w ↦ f (a - conj w)) =ᶠ[𝓝 z] fun w ↦ u * conj (f w)` and `u ≠ 0`, then
`logDeriv f (a - conj z) = -conj (logDeriv f z)`, with no differentiability assumption on `f`. -/
theorem logDeriv_sub_conj_nhds_of_ne_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [StarRing 𝕜] [NormedStarGroup 𝕜] {f : 𝕜 → 𝕜} {a u z : 𝕜}
    (hfe : (fun w : 𝕜 ↦ f (a - conj w)) =ᶠ[𝓝 z] fun w : 𝕜 ↦ u * conj (f w)) (hu : u ≠ 0) :
    logDeriv f (a - conj z) = -conj (logDeriv f z) := by
  have hconj : Tendsto (fun w : 𝕜 ↦ conj w) (𝓝 (conj z)) (𝓝 z) := by
    simpa [starRingEnd_apply] using (continuous_star (R := 𝕜)).tendsto (conj z)
  have hEq : (fun w : 𝕜 ↦ f (a - w)) =ᶠ[𝓝 (conj z)] fun w : 𝕜 ↦ u * (conj ∘ f ∘ conj) w := by
    filter_upwards [hconj.eventually hfe] with w hw
    simpa [Function.comp_def] using hw
  have hcongr : logDeriv (fun w : 𝕜 ↦ f (a - w)) (conj z) =
      logDeriv (fun w : 𝕜 ↦ u * (conj ∘ f ∘ conj) w) (conj z) := by
    rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
  rw [logDeriv_comp_const_sub, logDeriv_const_mul _ _ hu, logDeriv_conj_conj,
    starRingEnd_self_apply] at hcongr
  exact neg_eq_iff_eq_neg.mp hcongr

/-- **Local logarithmic-derivative symmetry under `w ↦ a - conj w`.** If
`(fun w ↦ f (a - conj w)) =ᶠ[𝓝 z] fun w ↦ u * conj (f w)` and the same germ identity holds at
`conj (a - z)`, then `logDeriv f (a - conj z) = -conj (logDeriv f z)` (including the degenerate
case `u = 0`). -/
theorem logDeriv_sub_conj_nhds {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [StarRing 𝕜] [NormedStarGroup 𝕜] {f : 𝕜 → 𝕜} {a u z : 𝕜}
    (hfe : (fun w : 𝕜 ↦ f (a - conj w)) =ᶠ[𝓝 z] fun w : 𝕜 ↦ u * conj (f w))
    (hfe' : (fun w : 𝕜 ↦ f (a - conj w)) =ᶠ[𝓝 (conj (a - z))] fun w : 𝕜 ↦ u * conj (f w)) :
    logDeriv f (a - conj z) = -conj (logDeriv f z) := by
  rcases eq_or_ne u 0 with rfl | hu
  · have h1 : f (a - conj z) = 0 := by simpa using hfe.eq_of_nhds
    have h2 : f z = 0 := by simpa [sub_sub_cancel] using hfe'.eq_of_nhds
    simp [logDeriv_apply, h1, h2]
  · exact logDeriv_sub_conj_nhds_of_ne_zero hfe hu

/-- Under a global functional-conjugation symmetry `f (a - z) = u * conj (f (conj z))`, the
logarithmic derivative satisfies `logDeriv f (a - conj z) = -conj (logDeriv f z)`. -/
theorem logDeriv_sub_conj {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [StarRing 𝕜] [NormedStarGroup 𝕜] {f : 𝕜 → 𝕜} {a u : 𝕜}
    (hfe : ∀ z : 𝕜, f (a - z) = u * conj (f (conj z))) (z : 𝕜) :
    logDeriv f (a - conj z) = -conj (logDeriv f z) :=
  logDeriv_sub_conj_nhds
    (Eventually.of_forall fun w ↦ by simpa using hfe (conj w))
    (Eventually.of_forall fun w ↦ by simpa using hfe (conj w))

end TauCeti
