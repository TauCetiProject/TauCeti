/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Integrability from polynomial decay at infinity

On a finite-dimensional real normed space of dimension `d`, a locally integrable function which is
`O((1 + ‖x‖) ^ (-r))` at infinity for some `r > d` is integrable, for every additive Haar measure.
This combines Mathlib's integrability of the Japanese bracket (`integrable_one_add_norm`) with its
criterion `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`.
-/

public section

namespace MeasureTheory

open Asymptotics Filter Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] {f : E → F}

/-- A locally integrable function on a finite-dimensional real normed space which is
`O((1 + ‖x‖) ^ (-r))` at infinity, with `r` larger than the dimension, is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_one_add_norm_rpow_neg
    (hf : LocallyIntegrable f μ) {r : ℝ} (hr : (finrank ℝ E : ℝ) < r)
    (ho : f =O[cocompact E] fun x ↦ (1 + ‖x‖) ^ (-r)) : Integrable f μ :=
  hf.integrable_of_isBigO_cocompact ho ((integrable_one_add_norm hr).integrableAtFilter _)

end MeasureTheory
