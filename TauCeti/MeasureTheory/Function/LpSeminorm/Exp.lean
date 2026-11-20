/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# `exp f - 1` for essentially bounded `Lᵖ` functions

The function `exp t - 1` vanishes at `0` and is Lipschitz on every bounded interval, with
`|exp t - 1| ≤ exp M |t|` for `|t| ≤ M` (`TauCeti.abs_exp_sub_one_le_mul_exp_abs`). Hence
`exp f - 1` lies in `Lᵖ` whenever `f` does and `f` is essentially bounded
(`MeasureTheory.MemLp.exp_sub_one`). This is the form in which exponential nonlinearities,
such as the one in Taubes's reduced vortex equation, are first shown to be integrable once a
solution is known to be bounded.

## Main results

* `MeasureTheory.MemLp.exp_sub_one`: if `f ∈ Lᵖ` and `|f| ≤ M` almost everywhere, then
  `exp f - 1 ∈ Lᵖ`.
-/

public section

open Filter

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ENNReal} {f : α → ℝ}

/-- If `f ∈ Lᵖ` and `|f| ≤ M` almost everywhere, then `exp f - 1 ∈ Lᵖ`, since
`|exp f - 1| ≤ exp M |f|`. -/
theorem MemLp.exp_sub_one (hf : MemLp f p μ) {M : ℝ} (hM : ∀ᵐ x ∂μ, |f x| ≤ M) :
    MemLp (fun x ↦ Real.exp (f x) - 1) p μ := by
  refine (hf.const_mul (Real.exp M)).of_le
    ((Real.continuous_exp.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub
      aestronglyMeasurable_const) ?_
  filter_upwards [hM] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos M), mul_comm]
  exact (TauCeti.abs_exp_sub_one_le_mul_exp_abs (f x)).trans (by gcongr)

end MeasureTheory
