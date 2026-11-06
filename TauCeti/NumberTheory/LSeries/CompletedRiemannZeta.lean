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
from `0` and `1`, and has a simple pole, of order exactly `-1`, at each of `0` and `1`. Since
`ζ(s) = Λ(s) / Γ_ℝ(s)` for `s ≠ 0` and `1 / Γ_ℝ` is entire, the Riemann zeta function itself is
meromorphic on `ℂ` too; this is what lets a factorization through `ζ` serve as a meromorphic
continuation.

## Main results

* `TauCeti.meromorphic_completedRiemannZeta`
* `TauCeti.analyticAt_completedRiemannZeta`
* `TauCeti.meromorphicOrderAt_completedRiemannZeta_zero`,
  `TauCeti.meromorphicOrderAt_completedRiemannZeta_one`
* `TauCeti.meromorphic_riemannZeta`: the uncompleted function `riemannZeta` is meromorphic on `ℂ`
  as well.
-/

public section

open Filter Topology

namespace TauCeti

/-- Mathlib's completed Riemann zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_completedRiemannZeta : Meromorphic completedRiemannZeta := by
  intro z
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ z := differentiable_completedZeta₀.analyticAt z
  rw [funext completedRiemannZeta_eq]
  fun_prop

/-- Mathlib's completed Riemann zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ s := differentiable_completedZeta₀.analyticAt s
  have h1' : 1 - s ≠ 0 := sub_ne_zero.2 h1.symm
  rw [funext completedRiemannZeta_eq]
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
  -- Transport the pole at `0` along the functional equation `completedRiemannZeta_one_sub`.
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta)
    (g := fun z : ℂ ↦ 1 - z) (x := 1) (by fun_prop) (by simp)
  rw [sub_self, meromorphicOrderAt_completedRiemannZeta_zero] at h
  rw [← h]
  congr 1
  exact funext fun z ↦ (completedRiemannZeta_one_sub z).symm

/-- Mathlib's Riemann zeta function is meromorphic on `ℂ`. Away from `1` it is analytic
(`analyticOn_riemannZeta`); its pole at `1` is that of `completedRiemannZeta`. -/
theorem meromorphic_riemannZeta : Meromorphic riemannZeta := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · refine ((meromorphic_completedRiemannZeta 1).mul
      (Complex.differentiable_Gammaℝ_inv.analyticAt 1).meromorphicAt).congr ?_
    filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds one_ne_zero)] with s hs
    rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv, Pi.mul_apply]
  · exact (analyticOn_riemannZeta z hz).meromorphicAt

end TauCeti
