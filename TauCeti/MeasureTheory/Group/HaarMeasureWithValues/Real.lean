/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Real
public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Basic

/-!
# Real-valued Haar measures from Haar measures

A left-invariant measure `m` on a topological group `G` that is finite on compact sets restricts to
an `ℝ`-valued Haar measure on the compact open subsets of `G`, `K ↦ m.real K`
(`TauCeti.HaarMeasureWithValues.ofMeasure`). By uniqueness of ring-valued Haar measures, when `m`
is a Haar measure and `U₀` is a compact open subgroup, the `ℝ`-valued Haar measure normalised on
`U₀` is `K ↦ m(K) / m(U₀)` (`TauCeti.HaarMeasureWithValues.normalized_real_apply`). So the volumes
of compact open sets defined over an arbitrary coefficient ring agree over `ℝ` with the ones given
by Mathlib's Haar measure, for instance `MeasureTheory.Measure.haar`.
-/

public section

open MeasureTheory TopologicalSpace
open scoped Pointwise

namespace TauCeti.HaarMeasureWithValues

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

/-- The `ℝ`-valued Haar measure `K ↦ m.real K` on the compact open subsets of `G` defined by a
left-invariant measure `m` that is finite on compact sets. -/
noncomputable def ofMeasure (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m] :
    HaarMeasureWithValues ℝ G where
  toFun K := m.real K
  map_bot' := by simp [Measure.real]
  map_sup' K L h := measureReal_union₀ L.isOpen.measurableSet.nullMeasurableSet h.aedisjoint
    K.isCompact.measure_lt_top.ne L.isCompact.measure_lt_top.ne
  map_smul' g K := by simp [Measure.real, measure_smul m g (K : Set G)]

@[simp]
theorem ofMeasure_apply (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (K : CompactOpens G) : ofMeasure m K = m.real K :=
  (rfl)

/-- **Comparison with Mathlib's Haar measures.** For a Haar measure `m` on `G` and a compact open
subgroup `U₀`, the `ℝ`-valued Haar measure normalised on `U₀` gives a compact open set `K` the
volume `m(K) / m(U₀)`. -/
theorem normalized_real_apply {U₀ : OpenSubgroup G} (hU₀ : IsCompact (U₀ : Set G))
    (h : HasUnitProOrder ℝ U₀) (m : Measure G) [m.IsHaarMeasure] (K : CompactOpens G) :
    normalized ℝ U₀ hU₀ h K = m.real K / m.real (U₀ : Set G) := by
  have h0 : m.real (U₀ : Set G) ≠ 0 :=
    (ENNReal.toReal_pos (U₀.isOpen.measure_ne_zero m ⟨1, U₀.one_mem⟩)
      hU₀.measure_lt_top.ne).ne'
  rw [eq_div_iff h0]
  simpa using ((ofMeasure m).apply_eq_normalized_mul hU₀ h K).symm

end TauCeti.HaarMeasureWithValues
