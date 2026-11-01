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

For a continuous real function `w` and `η > 0`, the clamped function `max 0 (min w η)` has
derivative equal to that of `w` on the open band `{0 < w < η}` and zero everywhere else, including
on the two levels `0` and `η`, where it attains a local extremum
(`TauCeti.fderiv_max_min_eq_indicator`). No differentiability of `w` is assumed: on the band the
clamped function agrees with `w` nearby, and off it the clamped function is locally constant or
has a local extremum.

Clamped functions of this form are the standard test functions for integration by parts against
the indicator of a superlevel set.
-/

public section

open Filter Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the clamped function `max 0 (min w η)` is the derivative of `w` on
`{0 < w < η}` and vanishes elsewhere, including at both levels `0` and `η`. -/
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
