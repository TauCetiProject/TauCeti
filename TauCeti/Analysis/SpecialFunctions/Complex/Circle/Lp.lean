/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The phase of a circle-valued `Lp` map

For a circle-valued map `u`, the logarithm `log u = log (1 + (u - 1))` is `i arg u`, because
`|u| = 1`. This file records the almost-everywhere form of this identity for `Lp`
representatives of `u - 1` and of its logarithm, as used when the phase of `u` is recovered from
the logarithm series in `u - 1`.

## Main results

* `Circle.neg_I_smul_ae_eq_arg`: if `L` represents `log (1 + (u - 1))` for a circle-valued `u`,
  then `-i L` represents the phase `arg u`.
-/

public section

open Complex MeasureTheory

namespace Circle

/-- **The phase of a circle-valued map is `-i log (1 + (u - 1))`.** For a circle-valued map `u`,
if `h` represents `u - 1` and `L` represents `log (1 + h)`, then `-i L` represents the phase
`arg u`, because `log u = i arg u` when `|u| = 1`. -/
theorem neg_I_smul_ae_eq_arg {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal}
    {u : α → Circle} {h L : Lp ℂ p μ} (hh : h =ᵐ[μ] (fun z ↦ (u z : ℂ) - 1))
    (hL : L =ᵐ[μ] (fun z ↦ log (1 + h z))) :
    ((-I) • L : Lp ℂ p μ) =ᵐ[μ] (fun z ↦ (arg (u z : ℂ) : ℂ)) := by
  filter_upwards [Lp.coeFn_smul (-I) L, hL, hh] with z hz hLz hhz
  rw [hz, Pi.smul_apply, smul_eq_mul, hLz, hhz, add_sub_cancel]
  apply Complex.ext <;> simp [log_re, log_im]

end Circle
