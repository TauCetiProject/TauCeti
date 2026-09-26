/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.MeasureTheory.Measure.Module

/-!
# Measures vanishing on a set form a face

Among the measures in any set `C` of measures, those giving mass zero to a fixed set `t` form a
face of `C`: a convex combination with positive weights vanishes on `t` only when both of its ends
do. Mathlib's `IsExtreme.extremePoints_eq` then reads the extreme points of the face off those of
`C`, which is how extremality among the laws carried by a set (vanishing on its complement)
reduces to extremality among all of `C`. When `C` is convex so is the face.

## Main results

* `TauCeti.MeasureTheory.isExtreme_setOf_measure_eq_zero` — the measures in `C` vanishing on `t`
  are a face of `C`.
* `TauCeti.MeasureTheory.extremePoints_setOf_measure_eq_zero` — their extreme points are the
  extreme points of `C` vanishing on `t`.
* `TauCeti.MeasureTheory.Convex.setOf_measure_eq_zero` — the face of a convex set is convex.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Among the measures in a set `C`, those vanishing on `t` form a face: neither end of a convex
combination with positive weights can charge `t` when the combination does not. -/
theorem isExtreme_setOf_measure_eq_zero (C : Set (Measure α)) (t : Set α) :
    IsExtreme ℝ≥0∞ C {μ ∈ C | μ t = 0} := by
  refine ⟨fun μ hμ => hμ.1, ?_⟩
  rintro μ₁ hμ₁ μ₂ hμ₂ μ ⟨-, hμ0⟩ ⟨a, b, ha, hb, -, rfl⟩
  have h : a * μ₁ t + b * μ₂ t = 0 := by
    simpa [Measure.add_apply, Measure.smul_apply] using hμ0
  rw [add_eq_zero, mul_eq_zero, mul_eq_zero] at h
  exact ⟨hμ₁, h.1.resolve_left ha.ne'⟩

/-- The extreme points of the measures in `C` vanishing on `t` are the extreme points of `C`
vanishing on `t`. -/
theorem extremePoints_setOf_measure_eq_zero (C : Set (Measure α)) (t : Set α) :
    extremePoints ℝ≥0∞ {μ ∈ C | μ t = 0} = {μ ∈ C | μ t = 0} ∩ extremePoints ℝ≥0∞ C :=
  (isExtreme_setOf_measure_eq_zero C t).extremePoints_eq

/-- The measures in a convex set vanishing on `t` form a convex set. -/
theorem _root_.Convex.setOf_measure_eq_zero {C : Set (Measure α)} (hC : Convex ℝ≥0∞ C)
    (t : Set α) : Convex ℝ≥0∞ {μ ∈ C | μ t = 0} := by
  rintro μ₁ ⟨hμ₁, h₁⟩ μ₂ ⟨hμ₂, h₂⟩ a b ha hb hab
  exact ⟨hC hμ₁ hμ₂ ha hb hab, by simp [Measure.add_apply, Measure.smul_apply, h₁, h₂]⟩

end TauCeti.MeasureTheory
