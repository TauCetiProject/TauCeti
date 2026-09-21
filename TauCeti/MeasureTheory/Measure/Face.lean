/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.MeasureTheory.Measure.Module

/-!
# Measures carried by a set form a face

Among the measures in a convex set `C`, those giving mass zero to the complement of a set `s` form
a face of `C`: a convex combination with positive weights vanishes on `sᶜ` only when both of its
ends do. Mathlib's `IsExtreme.extremePoints_eq` then reads the extreme points of the face off those
of `C`, which is how extremality among the laws carried by `s` reduces to extremality among all of
`C`.

## Main results

* `MeasureTheory.Measure.isExtreme_setOf_measure_compl_eq_zero` — the measures in `C` carried by
  `s` are a face of `C`.
* `MeasureTheory.Measure.extremePoints_setOf_measure_compl_eq_zero` — their extreme points are
  the extreme points of `C` carried by `s`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- Among the measures in a convex set, those carried by a set `s` (vanishing on `sᶜ`) form a
face: neither end of a convex combination with positive weights can charge `sᶜ` when the
combination does not. -/
theorem isExtreme_setOf_measure_compl_eq_zero (C : Set (Measure α)) (s : Set α) :
    IsExtreme ℝ≥0∞ C {μ ∈ C | μ sᶜ = 0} := by
  refine ⟨fun μ hμ => hμ.1, ?_⟩
  rintro μ₁ hμ₁ μ₂ hμ₂ μ ⟨-, hμ0⟩ ⟨a, b, ha, hb, -, rfl⟩
  have h : a * μ₁ sᶜ + b * μ₂ sᶜ = 0 := by
    simpa [Measure.add_apply, Measure.smul_apply] using hμ0
  rw [add_eq_zero, mul_eq_zero, mul_eq_zero] at h
  exact ⟨hμ₁, h.1.resolve_left ha.ne'⟩

/-- The extreme points of the measures in a convex set carried by `s` are the extreme points of
the whole set that are carried by `s`. -/
theorem extremePoints_setOf_measure_compl_eq_zero (C : Set (Measure α)) (s : Set α) :
    extremePoints ℝ≥0∞ {μ ∈ C | μ sᶜ = 0} = {μ ∈ C | μ sᶜ = 0} ∩ extremePoints ℝ≥0∞ C :=
  (isExtreme_setOf_measure_compl_eq_zero C s).extremePoints_eq

end MeasureTheory.Measure
