/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The constant one in `L∞`

This file defines the constant-one element of `L∞` on an arbitrary measure space. Unlike
`MeasureTheory.Lp.const`, the construction needs no finite-measure hypothesis because the
essential supremum of a constant is always finite. Every real `L∞` class `f` satisfies
`f ≤ ‖f‖ • 1` (`MeasureTheory.Lp.le_norm_smul_linftyOne`), so the constant one is an order unit,
and a positive linear functional on `L∞` is controlled by its value at one.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The constant-one element of `L∞(μ)`. -/
noncomputable def linftyOne : Lp ℝ ∞ μ :=
  (memLp_top_const (1 : ℝ)).toLp fun _ => 1

/-- The representative of `linftyOne` is almost everywhere the constant function one. -/
theorem coeFn_linftyOne :
    (linftyOne (Ω := Ω) (μ := μ) : Ω → ℝ) =ᵐ[μ] fun _ => 1 :=
  MemLp.coeFn_toLp (memLp_top_const (1 : ℝ))

end TauCeti

namespace MeasureTheory.Lp

open TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Every real `L∞` class lies below its norm times the constant one. With the lemmas of
`TauCeti/Analysis/Normed/Order/PositiveLinearMap.lean`, this bounds and makes continuous every
positive linear functional on `L∞`. -/
theorem le_norm_smul_linftyOne (f : Lp ℝ ∞ μ) : f ≤ ‖f‖ • linftyOne := by
  rw [← Lp.coeFn_le]
  filter_upwards [Lp.ae_norm_le_norm_top f, Lp.coeFn_smul ‖f‖ (linftyOne (μ := μ)),
    coeFn_linftyOne (μ := μ)] with x hx hs h1
  rw [hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]
  exact (le_abs_self _).trans hx

end MeasureTheory.Lp
