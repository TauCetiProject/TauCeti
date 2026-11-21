/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Densities of norm one from lower bounds on open sets

Let `μ` be a locally finite measure on a second countable topological space and let `g` be a
weight with `g ≤ 1` almost everywhere. If every open set `V` satisfies `μ V ≤ ∫⁻ x in V, g x ∂μ`,
then `g = 1` almost everywhere (`TauCeti.ae_eq_one_of_measure_le_setLIntegral`). This is the last
step of a polar decomposition `T = σ ‖T‖`: once the density `σ` of a functional with respect to its
variation measure `‖T‖` has norm at most one, testing the supremum that defines `‖T‖ V` against the
representation gives the lower bound on open sets, so `‖σ‖ = 1` almost everywhere.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §1.8 (the polar decomposition in the Riesz representation theorem).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- A weight `g ≤ 1` whose integral over every open set `V` is at least `μ V` equals one almost
everywhere, for a locally finite measure `μ` on a second countable space. -/
theorem ae_eq_one_of_measure_le_setLIntegral {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
    {g : X → ℝ≥0∞} (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) (hg : ∀ V, IsOpen V → μ V ≤ ∫⁻ x in V, g x ∂μ) :
    ∀ᵐ x ∂μ, g x = 1 := by
  -- Cover `X` by countably many open sets of finite measure.
  let S := μ.finiteSpanningSetsInOpen'
  rw [← Measure.restrict_univ (μ := μ), ← S.spanning, ae_restrict_iUnion_iff]
  intro n
  have hle : ∀ᵐ x ∂μ.restrict (S.set n), g x ≤ 1 := ae_restrict_of_ae hg1
  have hint : ∫⁻ x in S.set n, g x ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (S.finite n).ne ((lintegral_mono_ae hle).trans_eq (by simp))
  exact ae_eq_of_ae_le_of_lintegral_le hle hint aemeasurable_const
    (by simpa using hg _ (S.set_mem n))

end TauCeti
