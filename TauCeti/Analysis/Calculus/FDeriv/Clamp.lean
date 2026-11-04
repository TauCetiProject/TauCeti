/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# The derivative of a clamped function

For a continuous real function `w` and `η > 0`, Lean's totalized `fderiv` of the clamped function
`max 0 (min w η)` equals `fderiv w` on the open band `{0 < w < η}` and zero everywhere else
(`TauCeti.fderiv_max_min_eq_indicator`). No differentiability of `w` is assumed: on the band the
clamped function agrees with `w` nearby, and off the closed band it is locally constant. On the two
levels `0` and `η` the clamped function attains a local extremum, so its `fderiv` is zero there
either because it is differentiable with zero derivative or because `fderiv` is zero by
convention at a point of non-differentiability; the identity does not assert differentiability
there, and the clamped function is in general not differentiable at those levels.

Clamped functions of this form are the standard test functions for integration by parts against
the indicator of a superlevel set. The clamped function differs from `η` times the indicator of
`{w > 0}` by at most `η`, and only on the band `{0 < w < η}`
(`TauCeti.abs_mul_indicator_sub_max_min_le`), for any real function `w` on any type.
-/

public section

open Filter Set

namespace TauCeti

/-- The clamped function `max 0 (min w η)` differs from `η` times the indicator of `{w > 0}`
by at most `η`, and only on the band `{0 < w < η}`. -/
theorem abs_mul_indicator_sub_max_min_le {X : Type*} {w : X → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (x : X) :
    |η * {x | 0 < w x}.indicator 1 x - max 0 (min (w x) η)| ≤
      (w ⁻¹' Ioo 0 η).indicator (fun _ => η) x := by
  by_cases hxS : x ∈ w ⁻¹' Ioo 0 η
  · have h1 : 0 < w x := hxS.1
    have h2 : w x < η := hxS.2
    rw [indicator_of_mem hxS, indicator_of_mem (s := {x | 0 < w x}) h1, Pi.one_apply, mul_one,
      min_eq_left h2.le, max_eq_right h1.le, abs_le]
    constructor <;> linarith
  · rw [indicator_of_notMem hxS]
    rcases le_or_gt (w x) 0 with h | h
    · rw [indicator_of_notMem (s := {x | 0 < w x}) h.not_gt, mul_zero,
        max_eq_left ((min_le_left _ _).trans h), sub_zero, abs_zero]
    · have hηx : η ≤ w x := le_of_not_gt fun h' => hxS ⟨h, h'⟩
      rw [indicator_of_mem (s := {x | 0 < w x}) h, Pi.one_apply, mul_one, min_eq_right hηx,
        max_eq_right hη, sub_self, abs_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lean's totalized `fderiv` of the clamped function `max 0 (min w η)` is `fderiv w` on
`{0 < w < η}` and zero elsewhere. At the levels `0` and `η` this is an identity for `fderiv` only:
it does not assert that the clamped function is differentiable there, and in general it is not. -/
theorem fderiv_max_min_eq_indicator {w : E → ℝ} (hw : Continuous w) {η : ℝ} (hη : 0 < η)
    (x : E) :
    fderiv ℝ (fun y => max 0 (min (w y) η)) x = (w ⁻¹' Ioo 0 η).indicator (fderiv ℝ w) x := by
  rcases lt_trichotomy (w x) 0 with h | h | h
  · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) fun hx => (h.trans hx.1).false]
    refine (Filter.EventuallyEq.fderiv_eq (f := fun _ => (0 : ℝ)) ?_).trans (fderiv_const_apply _)
    filter_upwards [hw.continuousAt.eventually (gt_mem_nhds h)] with y hy
    exact max_eq_left ((min_le_left _ _).trans hy.le)
  · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) fun hx => (h ▸ hx.1).false]
    refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun y => ?_)
    simp only [h, min_eq_left hη.le, max_self]
    exact le_max_left _ _
  rcases lt_trichotomy (w x) η with h' | h' | h'
  · rw [indicator_of_mem (s := w ⁻¹' Ioo 0 η) ⟨h, h'⟩]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hw.continuousAt.eventually (lt_mem_nhds h),
      hw.continuousAt.eventually (gt_mem_nhds h')] with y hy hy'
    rw [min_eq_left hy'.le, max_eq_right hy.le]
  · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) fun hx => (h' ▸ hx.2).false]
    refine IsLocalMax.fderiv_eq_zero (Filter.Eventually.of_forall fun y => ?_)
    simp only [h', min_self, max_eq_right hη.le]
    exact max_le hη.le (min_le_right _ _)
  · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) fun hx => (hx.2.trans h').false]
    refine (Filter.EventuallyEq.fderiv_eq (f := fun _ => η) ?_).trans (fderiv_const_apply _)
    filter_upwards [hw.continuousAt.eventually (lt_mem_nhds h')] with y hy
    rw [min_eq_right hy.le, max_eq_right hη.le]

end TauCeti
