/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The constant one in `L∞`

This file defines the constant-one element of `L∞` on an arbitrary measure space. Unlike
`MeasureTheory.Lp.const`, the construction needs no finite-measure hypothesis because the
essential supremum of a constant is always finite.
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
