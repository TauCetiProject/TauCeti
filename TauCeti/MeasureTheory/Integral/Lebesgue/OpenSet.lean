/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Densities bounded by one that integrate to the measure of every open set

Let `μ` be a locally finite measure on a second countable space and let `f` be a weight with
`f ≤ 1` almost everywhere. If `μ V ≤ ∫⁻_V f dμ` for every open set `V`, then `f = 1` almost
everywhere. Testing only open sets suffices because the open sets of finite measure cover the
space by countably many of them.

This is how the polar density of a vector-valued measure is shown to have norm one: the density
has norm at most one, and the variation measure of each open set is a supremum of pairings that
are bounded by the integral of the norm of the density over that set.

## Main results

* `MeasureTheory.ae_eq_one_of_forall_isOpen_le_setLIntegral`: `f = 1` almost everywhere.
-/

public section

open Set Filter TopologicalSpace
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  {μ : Measure X} [IsLocallyFiniteMeasure μ] {f : X → ℝ≥0∞}

/-- A weight `f ≤ 1` with `μ V ≤ ∫⁻_V f dμ` on every open set `V` is `1` almost everywhere. -/
theorem ae_eq_one_of_forall_isOpen_le_setLIntegral (hf : ∀ᵐ x ∂μ, f x ≤ 1)
    (h : ∀ V, IsOpen V → μ V ≤ ∫⁻ x in V, f x ∂μ) : ∀ᵐ x ∂μ, f x = 1 := by
  set V := μ.finiteSpanningSetsInOpen'
  rw [← Measure.restrict_univ (μ := μ), ← V.spanning, ae_restrict_iUnion_iff]
  intro n
  have hle : ∀ᵐ x ∂μ.restrict (V.set n), f x ≤ 1 := ae_restrict_of_ae hf
  have hint : ∫⁻ x in V.set n, f x ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (V.finite n).ne ((lintegral_mono_ae hle).trans_eq (by simp))
  exact ae_eq_of_ae_le_of_lintegral_le hle hint aemeasurable_const
    (by simpa using h _ (V.set_mem n))

end MeasureTheory
