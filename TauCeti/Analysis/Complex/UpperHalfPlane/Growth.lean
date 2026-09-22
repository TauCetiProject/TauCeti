/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exponential decay on the upper half-plane

A function dominated by a strictly decreasing real exponential in the imaginary coordinate
tends to zero as that coordinate tends to infinity. This supplies the general asymptotic step
used when exponential decay in a cusp coordinate is converted into vanishing at the cusp.

-/

/- Formal source: the argument is the one proving
`UpperHalfPlane.IsZeroAtImInfty.of_exp_decay` in
`Mathlib/NumberTheory/ModularForms/Petersson.lean`. That statement bundles the decay rate into
an existential and lives behind the modular-forms import, so the unbundled form is restated
here for use with a cusp coordinate. -/

public section

open Asymptotics Filter UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- A function bounded by `exp (-c * im z)` for some `c > 0` tends to zero at imaginary
infinity. -/
theorem isZeroAtImInfty_of_isBigO_exp_neg {E : Type*} [NormedAddCommGroup E] {f : ℍ → E}
    {c : ℝ} (hc : 0 < c) (hf : f =O[atImInfty] fun z ↦ Real.exp (-c * z.im)) :
    IsZeroAtImInfty f := by
  refine hf.trans_tendsto <| (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hc)

/-- An exponential growth bound at `i∞` remains valid after increasing its integer rate. -/
theorem isBigO_exp_of_le (w : ℝ) (hw : 0 < w) {k k' : ℤ} (hkk' : k ≤ k') {f : ℍ → ℂ}
    (hf : f =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / w)) :
    f =O[atImInfty] fun z ↦ Real.exp (2 * Real.pi * (k' : ℝ) * z.im / w) := by
  refine hf.trans (Asymptotics.isBigO_of_le _ fun z ↦ ?_)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  apply (div_le_div_iff_of_pos_right hw).2
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hkk') (by positivity)) z.im_pos.le

end TauCeti.UpperHalfPlane
