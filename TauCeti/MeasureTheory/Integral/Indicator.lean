/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Measures of almost surely eventual limits of events

Under a finite measure, an almost surely eventual limit of measurable events of constant
measure has the same measure. The limiting event need not itself be measurable: its measurable
representative is the `liminf` of the approximating events. This allows event identities to pass
to limits without completeness of the ambient sigma-algebra.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace TauCeti

/-- An almost surely eventual limit of measurable events of constant measure has that measure.
The limiting event itself need not be measurable. -/
theorem measure_eq_of_ae_eventually_mem_iff {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {E : ℕ → Set Ω} {F : Set Ω} {a : ℝ≥0∞}
    (hmE : ∀ n, MeasurableSet (E n)) (hE : ∀ n, P (E n) = a)
    (hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E n ↔ ω ∈ F) : P F = a := by
  -- Replace the possibly nonmeasurable limit by its measurable eventual-event version.
  let L := liminf E atTop
  have hmL : MeasurableSet L := MeasurableSet.measurableSet_liminf hmE
  have hLF : L =ᵐ[P] F := by
    filter_upwards [hlim] with ω hω
    exact mem_liminf_iff_eventually_mem.trans ((eventually_congr hω).trans eventually_const)
  have hconv : Tendsto (fun n => P (E n)) atTop (𝓝 (P L)) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hmL hmE
    filter_upwards [hlim, hLF] with ω hω hLFω
    simpa only [hLFω] using hω
  have heq : P L = a :=
    tendsto_nhds_unique hconv (by simpa only [hE] using tendsto_const_nhds)
  exact (measure_congr hLF).symm.trans heq

end TauCeti
