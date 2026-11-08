/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# Normalized Haar measure on compact groups

This file normalizes Mathlib's Haar measure on a compact topological group to a probability
measure, and records its left, right, and inversion invariance. The right and inversion
invariances come from
`MeasureTheory.Measure.isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure` and
`MeasureTheory.Measure.isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure`, which hold for every
finite Haar measure on a locally compact group.

Since `haarProb` is a Haar measure and a probability measure, Mathlib's generic API applies to
it directly: `MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure` identifies it with
any other Haar probability measure, and `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_mul_right_eq_self` and `MeasureTheory.integral_inv_eq_self` give the
translation and inversion identities used for averaging representations.
-/

public section

open MeasureTheory Set

namespace TauCeti

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar probability measure on a compact topological group. -/
noncomputable def haarProb : Measure G :=
  ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar

/-- The definition of normalized Haar measure as a rescaling of Mathlib's Haar measure. -/
theorem haarProb_def :
    haarProb G = ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar := by
  rw [haarProb]

instance isProbabilityMeasure_haarProb : IsProbabilityMeasure (haarProb G) := by
  rw [haarProb_def]
  infer_instance

instance isHaarMeasure_haarProb : (haarProb G).IsHaarMeasure := by
  rw [haarProb_def]
  exact Measure.IsHaarMeasure.smul Measure.haar
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _))

/-- Normalized Haar measure is invariant under right multiplication. -/
instance isMulRightInvariant_haarProb : (haarProb G).IsMulRightInvariant :=
  Measure.isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure _

/-- Normalized Haar measure is invariant under inversion. -/
instance isInvInvariant_haarProb : (haarProb G).IsInvInvariant :=
  Measure.isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure _

end CompactGroup

end TauCeti
