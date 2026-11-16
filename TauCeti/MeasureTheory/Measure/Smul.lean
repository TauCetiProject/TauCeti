/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Scalar multiples and scalar pushforwards of measures

This file collects elementary lemmas about scalar multiples `a • μ` of measures and pushforwards
`μ.map (c • ·)` along scalar multiplication.

## Main results

* `MeasureTheory.Measure.pos_of_smul_le_smul`: if `a μ ≤ b μ` for a nonzero measure `μ`, with
  `a > 0`, then `b > 0`.
* `MeasureTheory.Measure.map_map_const_smul`: pushing forward a measure along scalar
  multiplication by `c` commutes with pushing forward along any measurable map that commutes with
  `c • ·`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

namespace Measure

/-- If `a μ ≤ b μ` for a nonzero measure `μ`, with `a > 0`, then `b > 0`. -/
theorem pos_of_smul_le_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : ℝ≥0∞}
    (ha : 0 < a) (h : a • μ ≤ b • μ) (hμ : μ ≠ 0) : 0 < b := by
  refine pos_iff_ne_zero.2 fun h0 => hμ ?_
  rw [h0, zero_smul, Measure.nonpos_iff_eq_zero'] at h
  exact (Measure.ennreal_smul_eq_zero.mp h).resolve_left ha.ne'

/-- Pushing forward a measure along scalar multiplication by `c` commutes with pushing forward
along any measurable map that commutes with `c • ·`. -/
theorem map_map_const_smul {R E F : Type*} [SMul R E] [SMul R F]
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableConstSMul R E] [MeasurableConstSMul R F]
    (μ : Measure E) {f : E → F} (hf : Measurable f) (c : R)
    (hsmul : ∀ x, f (c • x) = c • f x) :
    (μ.map (c • ·)).map f = (μ.map f).map (c • ·) := by
  rw [Measure.map_map hf (measurable_const_smul c),
    Measure.map_map (measurable_const_smul c) hf]
  congr 1
  exact funext hsmul

end Measure

end MeasureTheory
