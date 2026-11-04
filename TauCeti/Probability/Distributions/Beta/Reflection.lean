/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.HasLaw
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Reflection of Beta laws

Reflection about `1 / 2` exchanges the two shape parameters of a Beta law. This gives the
distribution of the complementary proportion `1 - X` directly from the law of `X`.
The density and measure identities hold for every pair of real parameters, preserving
Mathlib's density-based definition outside the positive probability range.

The measure identity uses `MeasurableEquiv.map_withDensity` and the invariance of Lebesgue
measure under `x ↦ 1 - x`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Reflecting the real Beta density exchanges its shape parameters. -/
@[simp]
theorem betaPDFReal_one_sub (a b x : ℝ) :
    betaPDFReal a b (1 - x) = betaPDFReal b a x := by
  have h : (0 < 1 - x ∧ 1 - x < 1) ↔ (0 < x ∧ x < 1) := by
    constructor <;> intro hx <;> constructor <;> linarith
  simp only [betaPDFReal, h, sub_sub_cancel]
  split_ifs
  · rw [beta_comm a b]
    ring
  · rfl

/-- Reflecting the extended nonnegative Beta density exchanges its shape parameters. -/
@[simp]
theorem betaPDF_one_sub (a b x : ℝ) :
    betaPDF a b (1 - x) = betaPDF b a x := by
  simp only [betaPDF, betaPDFReal_one_sub]

/-- The complementary proportion of a Beta law has the reversed shape parameters.
This identity also holds outside the positive probability range. -/
@[simp]
theorem betaMeasure_map_one_sub (a b : ℝ) :
    (betaMeasure a b).map (fun x ↦ 1 - x) = betaMeasure b a := by
  have h := (MeasurableEquiv.subLeft (1 : ℝ)).map_withDensity volume (betaPDF a b)
  -- The equivalence writes its inverse as `-x + 1`; expose it as the same reflection.
  simpa [MeasurableEquiv.subLeft, Equiv.subLeft, betaMeasure,
    Measure.map_sub_left_eq_self, neg_add_eq_sub] using h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- Taking the complementary proportion of a Beta random variable exchanges its shapes. -/
theorem HasLaw.one_sub_betaMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {a b : ℝ} (hX : HasLaw X (betaMeasure a b) P) :
    HasLaw (fun ω ↦ 1 - X ω) (betaMeasure b a) P := by
  rw [← betaMeasure_map_one_sub]
  exact (hasLaw_map (measurable_const.sub measurable_id).aemeasurable).fun_comp hX

end ProbabilityTheory
