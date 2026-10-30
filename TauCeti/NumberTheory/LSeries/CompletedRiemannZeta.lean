/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Meromorphy and poles of the completed Riemann zeta function

Mathlib's `completedRiemannZeta` is `Λ(s) = Λ₀(s) - 1/s - 1/(1 - s)` with `Λ₀` entire
(`completedRiemannZeta_eq`, `differentiable_completedZeta₀`). This file reads off the
consequences in the language of meromorphic functions: `Λ` is meromorphic on `ℂ`, analytic away
from `0` and `1`, and has a simple pole, of order exactly `-1`, at each of `0` and `1`.

## Main results

* `TauCeti.meromorphic_completedRiemannZeta`
* `TauCeti.analyticAt_completedRiemannZeta`
* `TauCeti.meromorphicOrderAt_completedRiemannZeta_zero`,
  `TauCeti.meromorphicOrderAt_completedRiemannZeta_one`
-/

public section

open Filter Topology

namespace TauCeti

/-- Mathlib's completed Riemann zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_completedRiemannZeta : Meromorphic completedRiemannZeta := by
  intro z
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ z := differentiable_completedZeta₀.analyticAt z
  rw [show completedRiemannZeta = fun s ↦ completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) from
    funext completedRiemannZeta_eq]
  fun_prop

/-- Mathlib's completed Riemann zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ s := differentiable_completedZeta₀.analyticAt s
  have h1' : 1 - s ≠ 0 := sub_ne_zero.2 h1.symm
  rw [show completedRiemannZeta = fun s ↦ completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) from
    funext completedRiemannZeta_eq]
  fun_prop (disch := assumption)

/-- The completed Riemann zeta function has a simple pole at `0`. -/
theorem meromorphicOrderAt_completedRiemannZeta_zero :
    meromorphicOrderAt completedRiemannZeta 0 = (-1 : ℤ) := by
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ 0 := differentiable_completedZeta₀.analyticAt 0
  have h1 : (1 : ℂ) - 0 ≠ 0 := by norm_num
  refine (meromorphicOrderAt_eq_int_iff (meromorphic_completedRiemannZeta 0)).2
    ⟨fun z ↦ z * completedRiemannZeta₀ z - 1 - z / (1 - z), by fun_prop (disch := assumption),
      by simp, ?_⟩
  filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin (zero_ne_one (α := ℂ))]
    with z (hz : z ≠ 0) hz1
  have hz1' : 1 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  rw [completedRiemannZeta_eq, sub_zero, zpow_neg_one, smul_eq_mul]
  field_simp

/-- The completed Riemann zeta function has a simple pole at `1`. -/
theorem meromorphicOrderAt_completedRiemannZeta_one :
    meromorphicOrderAt completedRiemannZeta 1 = (-1 : ℤ) := by
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ 1 := differentiable_completedZeta₀.analyticAt 1
  have h1 : (1 : ℂ) ≠ 0 := one_ne_zero
  refine (meromorphicOrderAt_eq_int_iff (meromorphic_completedRiemannZeta 1)).2
    ⟨fun z ↦ (z - 1) * completedRiemannZeta₀ z - (z - 1) / z + 1,
      by fun_prop (disch := assumption), by simp, ?_⟩
  filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin (one_ne_zero (α := ℂ))]
    with z (hz : z ≠ 1) hz0
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.2 hz
  have hz1' : 1 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  rw [completedRiemannZeta_eq, zpow_neg_one, smul_eq_mul]
  field_simp
  ring

end TauCeti
