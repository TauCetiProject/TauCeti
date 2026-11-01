/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The constant one in `L∞`

This file equips `L∞(μ)` with the class `1` of the constant function one, for any normed group
with a distinguished element `1` and on an arbitrary measure space. Unlike
`MeasureTheory.Lp.const`, the construction needs no finite-measure hypothesis because the
essential supremum of a constant is always finite. Its norm is that of `1` unless `μ = 0`.
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E] [One E]

/-- The class of the constant function one, as an element of `L∞(μ)`. -/
instance inftyOne : One (Lp E ∞ μ) where
  one := (memLp_top_const (1 : E)).toLp fun _ => 1

theorem one_def : (1 : Lp E ∞ μ) = (memLp_top_const (1 : E)).toLp fun _ => 1 :=
  rfl

/-- The representative of `1 : L∞(μ)` is almost everywhere the constant function one. -/
theorem coeFn_one : ((1 : Lp E ∞ μ) : α → E) =ᵐ[μ] 1 :=
  MemLp.coeFn_toLp (memLp_top_const (1 : E))

/-- On a nonzero measure, the norm of `1 : L∞(μ)` is that of `1`. -/
theorem norm_one_of_ne_zero (hμ : μ ≠ 0) : ‖(1 : Lp E ∞ μ)‖ = ‖(1 : E)‖ := by
  rw [norm_def, eLpNorm_congr_ae coeFn_one, Pi.one_def,
    eLpNorm_exponent_top aestronglyMeasurable_const, eLpNormEssSup_const _ hμ, toReal_enorm]

end MeasureTheory.Lp
