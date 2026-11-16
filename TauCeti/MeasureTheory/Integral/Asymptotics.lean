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
criterion `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`. In particular a
continuous function with `(1 + ‖x‖) ^ N ‖f x‖` bounded for some integer `N > d` is integrable.
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

/-- A continuous function on a finite-dimensional real normed space such that `(1 + ‖x‖) ^ N ‖f x‖`
is bounded, for an integer `N` larger than the dimension, is integrable. -/
theorem integrable_of_one_add_norm_pow_mul_norm_le (hf : Continuous f) {N : ℕ}
    (hN : finrank ℝ E < N) {C : ℝ} (h : ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C) : Integrable f μ := by
  refine ((integrable_one_add_norm (μ := μ) (r := N) (mod_cast hN)).const_mul C).mono'
    hf.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity), mul_comm]
  exact h x

end MeasureTheory
