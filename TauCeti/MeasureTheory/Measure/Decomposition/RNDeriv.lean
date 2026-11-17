/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Square roots of Radon–Nikodym derivatives

The square root `√(dμ/dν)` of the density of a finite measure `μ` is square-integrable with
respect to any reference measure `ν`
(`MeasureTheory.Measure.memLp_two_sqrt_toReal_rnDeriv`), since its square integrates to at most
the mass of `μ`. Square roots of densities are the objects compared in `L²(ν)` by the Hellinger
distance.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- The square root `√(dμ/dν)` of the density of a finite measure `μ` is square-integrable,
whatever the reference measure `ν`: its square integrates to at most the mass of `μ`. -/
theorem memLp_two_sqrt_toReal_rnDeriv (μ ν : Measure α) [IsFiniteMeasure μ] :
    MemLp (fun x ↦ √(μ.rnDeriv ν x).toReal) 2 ν := by
  refine (memLp_two_iff_integrable_sq
    (μ.measurable_rnDeriv _).ennreal_toReal.sqrt.aestronglyMeasurable).mpr ?_
  simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using integrable_toReal_rnDeriv

end MeasureTheory.Measure
