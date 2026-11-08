/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Normalized Haar measure on compact groups

This file normalizes Mathlib's Haar measure on a compact topological group to a probability
measure, and records its left, right, and inversion invariance. These invariances hold for every
finite Haar measure on a locally compact group, since such a measure is determined by its total
mass.

Since `haarProb` is a Haar measure and a probability measure, Mathlib's generic API applies to
it directly: `MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure` identifies it with
any other Haar probability measure, and `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_mul_right_eq_self` and `MeasureTheory.integral_inv_eq_self` give the
translation and inversion identities used for averaging representations.
-/

public section

open MeasureTheory Set

namespace TauCeti

section LocallyCompactGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Two finite Haar measures on a locally compact group with the same total mass coincide. -/
theorem isHaarMeasure_eq_of_isFiniteMeasure_of_measure_univ_eq (μ' μ : Measure G)
    [μ'.IsHaarMeasure] [μ.IsHaarMeasure] [IsFiniteMeasure μ] (h : μ' univ = μ univ) :
    μ' = μ := by
  have : CompactSpace G := by
    by_contra H
    rw [not_compactSpace_iff] at H
    exact measure_ne_top μ univ (measure_univ_of_isMulLeftInvariant μ)
  obtain ⟨c, rfl⟩ : ∃ c : NNReal, μ' = c • μ :=
    ⟨_, Measure.isMulInvariant_eq_smul_of_compactSpace μ' μ⟩
  have hc : (c : ENNReal) * μ univ = 1 * μ univ := by simpa using h
  rw [ENNReal.mul_left_inj (NeZero.ne _) (measure_ne_top _ _), ENNReal.coe_eq_one] at hc
  rw [hc, one_smul]

/-- Every finite Haar measure on a locally compact group is right-invariant. -/
theorem isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsFiniteMeasure μ] : μ.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : (Measure.map (· * g) μ).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ g
    refine isHaarMeasure_eq_of_isFiniteMeasure_of_measure_univ_eq _ _ ?_
    rw [Measure.map_apply (measurable_mul_const g) .univ, preimage_univ]

/-- Every finite Haar measure on a locally compact group is invariant under inversion. -/
theorem isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsFiniteMeasure μ] : μ.IsInvInvariant := by
  have : μ.IsMulRightInvariant := isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure μ
  have : μ.inv.IsHaarMeasure := { }
  exact ⟨isHaarMeasure_eq_of_isFiniteMeasure_of_measure_univ_eq _ _ <| by
    simp [Measure.inv_apply]⟩

end LocallyCompactGroup

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
  isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure _

/-- Normalized Haar measure is invariant under inversion. -/
instance isInvInvariant_haarProb : (haarProb G).IsInvInvariant :=
  isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure _

end CompactGroup

end TauCeti
