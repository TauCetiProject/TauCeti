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
touch the slit-plane boundary, and along `w ↦ 1 - t * w` (`t ≥ 0`) for radial integrals
whose parameter approaches the cut `[1, ∞)` from the closed lower half-plane.

## Main declarations

* `TauCeti.continuousOn_arg_im_nonneg_ne_zero`.
* `TauCeti.continuousOn_log_im_nonneg_ne_zero`.
* `TauCeti.continuousOn_cpow_const_im_nonneg`.
* `TauCeti.tendsto_one_sub_ofReal_mul_nhdsWithin_im_nonpos`,
  `TauCeti.tendsto_one_sub_nhdsWithin_im_nonpos`.

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

open Filter in
open scoped Topology in
/-- For real `t ≥ 0` and `z : ℂ` with `1 - t * z ≠ 0`, the affine map `w ↦ 1 - t * w` sends
`𝓝[{w | w.im ≤ 0}] z` into `𝓝[{u | 0 ≤ u.im ∧ u ≠ 0}] (1 - t * z)`. -/
theorem tendsto_one_sub_ofReal_mul_nhdsWithin_im_nonpos {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : 1 - (t : ℂ) * z ≠ 0) :
    Tendsto (fun w : ℂ ↦ 1 - (t : ℂ) * w) (𝓝[{w : ℂ | w.im ≤ 0}] z)
      (𝓝[{u : ℂ | 0 ≤ u.im ∧ u ≠ 0}] (1 - (t : ℂ) * z)) := by
  have hcont : Continuous fun w : ℂ ↦ 1 - (t : ℂ) * w := by fun_prop
  refine tendsto_nhdsWithin_iff.mpr ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hcont.continuousAt.eventually_ne hz)] with w hw hw_ne
  refine ⟨?_, hw_ne⟩
  simp only [sub_im, one_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_sub]
  nlinarith [ht, hw]

open Filter in
open scoped Topology in
/-- For `z : ℂ` with `1 - z ≠ 0`, `w ↦ 1 - w` sends `𝓝[{w | w.im ≤ 0}] z` into
`𝓝[{u | 0 ≤ u.im ∧ u ≠ 0}] (1 - z)`. -/
theorem tendsto_one_sub_nhdsWithin_im_nonpos {z : ℂ} (hz : 1 - z ≠ 0) :
    Tendsto (fun w : ℂ ↦ 1 - w) (𝓝[{w : ℂ | w.im ≤ 0}] z)
      (𝓝[{u : ℂ | 0 ≤ u.im ∧ u ≠ 0}] (1 - z)) := by
  simpa using tendsto_one_sub_ofReal_mul_nhdsWithin_im_nonpos zero_le_one (by simpa using hz)

end TauCeti

end
