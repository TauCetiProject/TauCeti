/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# The derivative of a clamped function

For any real function `w` on a real normed space and any `c : ℝ`, Lean's totalized `fderiv` of the
one-sided clamp `max w c` equals `fderiv w` on `{w > c}` and zero elsewhere
(`TauCeti.fderiv_max_const_eq_indicator`), and symmetrically `fderiv` of `min w c` equals
`fderiv w` on `{w < c}` and zero elsewhere (`TauCeti.fderiv_min_const_eq_indicator`). Combining
the two yields that for arbitrary `a b : ℝ`, `fderiv` of the two-sided clamp `max a (min w b)`
equals `fderiv w` on the open band `{a < w < b}` and zero everywhere else
(`TauCeti.fderiv_max_min_eq_indicator`).

No continuity or differentiability of `w` is assumed: where `w ≤ c` the clamped function `max w c`
attains a global minimum so its `fderiv` vanishes, while where `w > c` either `w` is differentiable
(hence continuous, so `max w c` agrees with `w` nearby) or neither `w` nor `max w c` is
differentiable and both totalized derivatives vanish by convention. At the threshold levels these
identities concern `fderiv` only and do not assert differentiability.

Clamped functions of this form are the standard test functions for integration by parts against
the indicator of a superlevel set. The clamped function `max 0 (min w η)` differs from `η` times
the indicator of `{w > 0}` by at most `η`, and only on the band `{0 < w < η}`
(`TauCeti.abs_mul_indicator_sub_max_min_le`), for any real function `w` on any type. Against a
real weight `d`, the error is at most `η |d|` on the band
(`TauCeti.norm_mul_sub_clamp_le_indicator`).
-/

public section

open Filter Set
open scoped Topology

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

/-- The clamped function `max 0 (min w η)` agrees with `η 1_{w > 0}` off the shell `{0 < w < η}`
and differs from it by at most `η` on the shell; so against any `d` the error is at most
`η |d|` on the shell and zero off it. -/
theorem norm_mul_sub_clamp_le_indicator {X : Type*} {w : X → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (d : ℝ) (x : X) :
    ‖d * (η * {x | 0 < w x}.indicator 1 x - max 0 (min (w x) η))‖ ≤
      η * (w ⁻¹' Ioo 0 η).indicator (fun _ => |d|) x := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_left (abs_mul_indicator_sub_max_min_le (w := w) hη x)
    (abs_nonneg d)).trans_eq ?_
  rw [mul_comm, ← indicator_const_mul, ← indicator_mul_const]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lean's totalized `fderiv` of the lower-clamped function `max w c` equals `fderiv w` on
`{w > c}` and zero elsewhere, with no continuity or differentiability hypothesis on `w`. -/
theorem fderiv_max_const_eq_indicator (w : E → ℝ) (c : ℝ) (x : E) :
    fderiv ℝ (fun y ↦ max (w y) c) x = (w ⁻¹' Ioi c).indicator (fderiv ℝ w) x := by
  rcases le_or_gt (w x) c with hxc | hcx
  · rw [indicator_of_notMem (s := w ⁻¹' Ioi c) hxc.not_gt]
    refine IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ ?_)
    simp [max_eq_right hxc]
  · rw [indicator_of_mem (s := w ⁻¹' Ioi c) hcx]
    by_cases hw : DifferentiableAt ℝ w x
    · refine EventuallyEq.fderiv_eq ?_
      filter_upwards [hw.continuousAt.eventually (lt_mem_nhds hcx)] with y hy
      exact max_eq_left hy.le
    · rw [fderiv_zero_of_not_differentiableAt hw]
      refine fderiv_zero_of_not_differentiableAt fun hm ↦ hw ?_
      have hmx : c < max (w x) c := by rwa [max_eq_left hcx.le]
      have hev : (fun y ↦ max (w y) c) =ᶠ[𝓝 x] w := by
        filter_upwards [hm.continuousAt.eventually (lt_mem_nhds hmx)] with y hy
        exact max_eq_left (le_of_not_gt fun hyc ↦ hy.ne' (max_eq_right hyc.le))
      exact hm.congr_of_eventuallyEq hev.symm

/-- Lean's totalized `fderiv` of the upper-clamped function `min w c` equals `fderiv w` on
`{w < c}` and zero elsewhere, with no continuity or differentiability hypothesis on `w`. -/
theorem fderiv_min_const_eq_indicator (w : E → ℝ) (c : ℝ) (x : E) :
    fderiv ℝ (fun y ↦ min (w y) c) x = (w ⁻¹' Iio c).indicator (fderiv ℝ w) x := by
  have hmin : (fun y ↦ min (w y) c) = -(fun y ↦ max ((-w) y) (-c)) := by
    ext y
    simp only [Pi.neg_apply]
    grind
  have hpre : (-w) ⁻¹' Ioi (-c) = w ⁻¹' Iio c := by
    ext y
    exact neg_lt_neg_iff
  rw [hmin, fderiv_neg, fderiv_max_const_eq_indicator (-w) (-c), hpre]
  by_cases hx : x ∈ w ⁻¹' Iio c
  · rw [indicator_of_mem hx, indicator_of_mem hx, fderiv_neg, neg_neg]
  · simp [hx]

/-- Lean's totalized `fderiv` of the clamped function `max a (min w b)` equals `fderiv w` on
`{a < w < b}` and zero elsewhere, for arbitrary `w : E → ℝ` and `a b : ℝ`. At the levels `a` and
`b` this is an identity for `fderiv` only and does not assert differentiability. -/
theorem fderiv_max_min_eq_indicator (w : E → ℝ) (a b : ℝ) (x : E) :
    fderiv ℝ (fun y ↦ max a (min (w y) b)) x = (w ⁻¹' Ioo a b).indicator (fderiv ℝ w) x := by
  simp_rw [max_comm a]
  rw [fderiv_max_const_eq_indicator, funext (fderiv_min_const_eq_indicator w b),
    indicator_indicator]
  congr 1
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_Iio, mem_Ioo, lt_min_iff]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.1.trans h.2⟩, h.2⟩⟩

end TauCeti
