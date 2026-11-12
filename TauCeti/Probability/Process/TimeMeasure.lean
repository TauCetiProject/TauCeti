/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Lebesgue time measure on a finite nonnegative horizon

`TauCeti.Probability.timeMeasure T` is Lebesgue measure on `(0,T]` in nonnegative real
time, obtained by pulling back real Lebesgue measure along the coercion to `ℝ`.
The origin has zero mass. Interval masses and restriction to shorter horizons are
recorded explicitly for time-product measures used in stochastic integration.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- Lebesgue measure on the finite time horizon `(0,T]`, with no atom at time zero. -/
noncomputable def timeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  (Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 T)

/-- The real-Lebesgue pullback defining the finite-horizon time measure. -/
theorem timeMeasure_def (T : ℝ≥0) :
    timeMeasure T = (Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 T) :=
  (rfl)

/-- The mass of a measurable time set is its real Lebesgue mass within the horizon. -/
theorem timeMeasure_apply (T : ℝ≥0) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    timeMeasure T s = volume (((↑) : ℝ≥0 → ℝ) '' (s ∩ Ioc 0 T)) := by
  rw [timeMeasure_def, Measure.restrict_apply hs,
    (NNReal.isClosedEmbedding_coe.measurableEmbedding).comap_apply]

/-- A time interval has its Lebesgue length, truncated at the horizon. -/
@[simp]
theorem timeMeasure_Ioc (T s t : ℝ≥0) :
    timeMeasure T (Ioc s t) = ENNReal.ofReal ((min t T : ℝ≥0) - (s : ℝ)) := by
  simp [timeMeasure_apply T measurableSet_Ioc, Ioc_inter_Ioc,
    NNReal.image_coe_Ioc, Real.volume_Ioc]

/-- An initial closed interval has its length clipped at the horizon; time zero is null. -/
@[simp]
theorem timeMeasure_Iic (T t : ℝ≥0) : timeMeasure T (Iic t) = (min t T : ℝ≥0) := by
  rw [timeMeasure_apply T measurableSet_Iic, inter_comm, Ioc_inter_Iic]
  simp [NNReal.image_coe_Ioc, Real.volume_Ioc, min_comm]

/-- The total time mass is the length of the horizon. -/
@[simp]
theorem timeMeasure_univ (T : ℝ≥0) : timeMeasure T univ = T := by
  calc
    timeMeasure T univ = timeMeasure T (Ioc 0 T) := by
      rw [timeMeasure_def, Measure.restrict_apply_univ, Measure.restrict_apply_self]
    _ = T := by simp

/-- Finite time horizons have finite time mass. -/
instance (T : ℝ≥0) : IsFiniteMeasure (timeMeasure T) :=
  ⟨by simp⟩

/-- Finite linear combinations of initial-interval indicators are dense in the
finite-horizon time `L²` space. -/
theorem topologicalClosure_span_indicatorConstLp_Iic (T : ℝ≥0) :
    (Submodule.span ℝ (range fun t : ℝ≥0 ↦
      indicatorConstLp (μ := timeMeasure T) 2 (measurableSet_Iic (a := t))
        (measure_ne_top _ _) (1 : ℝ))).topologicalClosure = ⊤ := by
  have hgen : (inferInstance : MeasurableSpace ℝ≥0) =
      MeasurableSpace.generateFrom (range Iic) := by
    exact (BorelSpace.measurable_eq (α := ℝ≥0)).trans (borel_eq_generateFrom_Iic ℝ≥0)
  have hcover : IsCountablySpanning (range (Iic : ℝ≥0 → Set ℝ≥0)) := by
    refine ⟨fun n : ℕ ↦ Iic (n : ℝ≥0), fun n ↦ mem_range_self _, ?_⟩
    ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge t
  have hdense := TauCeti.topologicalClosure_span_indicatorConstLp_eq_top_of_isPiSystem
    (μ := timeMeasure T) hgen isPiSystem_Iic hcover (fun _ _ ↦ measure_ne_top _ _)
  have hset : {g : Lp ℝ 2 (timeMeasure T) |
      ∃ (s : Set ℝ≥0) (hs : s ∈ range Iic),
        g = indicatorConstLp 2 (hgen ▸ MeasurableSpace.measurableSet_generateFrom hs)
          (measure_ne_top _ _) 1} = range (fun t : ℝ≥0 ↦
        indicatorConstLp (μ := timeMeasure T) 2 (measurableSet_Iic (a := t))
          (measure_ne_top _ _) (1 : ℝ)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact mem_range_self t
    · rintro ⟨t, rfl⟩
      exact ⟨Iic t, mem_range_self t, rfl⟩
  rwa [hset] at hdense

/-- The horizon of length zero carries the zero measure. -/
@[simp]
theorem timeMeasure_zero : timeMeasure 0 = 0 := by
  simp [timeMeasure_def]

/-- The initial time carries no mass, independently of the horizon. -/
@[simp]
theorem timeMeasure_singleton_zero (T : ℝ≥0) : timeMeasure T {0} = 0 := by
  simp [timeMeasure_apply T (measurableSet_singleton 0)]

/-- Restricting time measure again clips the horizon to the smaller endpoint. -/
@[simp]
theorem timeMeasure_restrict (T S : ℝ≥0) :
    (timeMeasure T).restrict (Ioc 0 S) = timeMeasure (min S T) := by
  rw [timeMeasure_def, Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc]
  simp [timeMeasure_def]

end TauCeti.Probability
