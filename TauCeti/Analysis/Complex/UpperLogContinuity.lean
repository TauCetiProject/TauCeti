/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuity of `arg` and `log` on the closed upper half-plane

The principal argument and logarithm are continuous on the punctured closed upper
half-plane `{z | 0 ≤ im z ∧ z ≠ 0}`. This strengthens Mathlib's continuity on the open
slit plane: the negative real axis is allowed because the approach is confined to
nonnegative imaginary parts, where `arg` agrees with the continuous `arccos` formula.
It is the boundary-tolerant ingredient for logarithmic primitives along contours that
touch the slit-plane boundary.

## Main declarations

* `TauCeti.continuousOn_arg_im_nonneg_ne_zero`.
* `TauCeti.continuousOn_log_im_nonneg_ne_zero`.
* `TauCeti.continuousOn_cpow_const_im_nonneg`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/Common.lean`) this file ports
  onto the current Mathlib pin.
-/

public section

open Complex

namespace TauCeti

/-- The principal argument is continuous on the punctured closed upper half-plane, including
one-sided continuity at the negative real axis. -/
@[fun_prop]
theorem continuousOn_arg_im_nonneg_ne_zero :
    ContinuousOn arg {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} :=
  -- On this set `arg` agrees with the continuous `arccos` formula.
  ((continuous_re.continuousOn.div continuous_norm.continuousOn fun _ (hz : _ ∧ _) ↦
    norm_ne_zero_iff.2 hz.2).arccos).congr fun _ hz ↦ arg_of_im_nonneg_of_ne_zero hz.1 hz.2

/-- The principal logarithm is continuous on the punctured closed upper half-plane, including
one-sided continuity at the negative real axis. -/
@[fun_prop]
theorem continuousOn_log_im_nonneg_ne_zero :
    ContinuousOn log {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  unfold log
  fun_prop (disch := exact fun _ hz ↦ norm_ne_zero_iff.2 hz.2)

/-- A complex power whose exponent has positive real part is continuous on the closed upper
half-plane. Unlike continuity on the open slit plane, this includes one-sided continuity at the
negative real axis; positivity of the exponent's real part also supplies continuity at zero. -/
@[fun_prop]
theorem continuousOn_cpow_const_im_nonneg {r : ℂ} (hr : 0 < r.re) :
    ContinuousOn (fun z : ℂ ↦ z ^ r) {z | 0 ≤ z.im} := by
  intro z hz
  obtain rfl | hz0 := eq_or_ne z 0
  · exact (continuousAt_cpow_const_of_re_pos (Or.inl zero_re.ge) hr).continuousWithinAt
  · -- Away from zero, `z ^ r = exp (log z * r)` and the puncture is a neighbourhood of `z`.
    refine ContinuousWithinAt.mono_of_mem_nhdsWithin (t := {z : ℂ | 0 ≤ z.im ∧ z ≠ 0}) ?_ ?_
    · exact ((continuousOn_log_im_nonneg_ne_zero.mul continuousOn_const).cexp.congr
        fun w hw ↦ cpow_def_of_ne_zero hw.2 r) z ⟨hz, hz0⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_ne_nhds hz0)]
        with w hw hw0 using ⟨hw, hw0⟩

end TauCeti

end
