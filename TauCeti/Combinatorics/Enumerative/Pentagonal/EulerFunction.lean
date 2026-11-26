/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import TauCeti.Analysis.Analytic.TaylorSeries
import TauCeti.RingTheory.PowerSeries.Radius

/-!
# The Taylor series of the Euler function

The pentagonal series is preserved by coefficient ring maps and has constant coefficient one.
It gives the analytic expansion of the Euler function on the open unit ball, allowing Euler
products to be compared with formal power series over other coefficient rings.
-/

public section

open PowerSeries

namespace PowerSeries

/-- Applying a coefficient ring homomorphism to the pentagonal series preserves the series. -/
@[simp]
theorem map_pentagonalSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (pentagonalSeries R).map f = pentagonalSeries S := by
  ext n
  have hR := coeff_pentagonalSeries_mul_eq_extend R n (fun _ ↦ 1)
  have hS := coeff_pentagonalSeries_mul_eq_extend S n (fun _ ↦ 1)
  simp only [mul_one] at hR hS
  rw [coeff_map, hR, hS, Function.apply_extend ⇑f]
  simp [Function.comp_def, Int.coe_negOnePow, Pi.zero_def]

/-- The pentagonal series has constant coefficient one. -/
@[simp]
theorem constantCoeff_pentagonalSeries (R : Type*) [CommRing R] :
    constantCoeff (pentagonalSeries R) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    ← show pentagonal 0 = 0 by norm_num [pentagonal_def], coeff_pentagonalSeries_pentagonal]
  simp

end PowerSeries

namespace TauCeti

/-- The Euler function takes the value one at zero. -/
@[simp]
theorem eulerFunction_zero {R : Type*} [NormedCommRing R] : eulerFunction (0 : R) = 1 := by
  rw [eulerFunction_def, tsum_eq_single 0]
  · simp [coeff_zero_eq_constantCoeff_apply]
  · intro n hn
    simp [zero_pow hn]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- The Euler function is represented on the open unit ball by the pentagonal series. -/
theorem hasFPowerSeriesOnBall_eulerFunction : HasFPowerSeriesOnBall (eulerFunction : 𝕜 → 𝕜)
    (.ofScalars 𝕜 (fun n ↦ (pentagonalSeries 𝕜).coeff n)) 0 1 := by
  have hrad := PowerSeries.le_radius_of_bound (f := pentagonalSeries 𝕜) 1 (r := 1) (fun n ↦ by
    simp only [NNReal.coe_one, one_pow, mul_one]
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨k, rfl⟩ := hn
      simp [Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn])
  refine ⟨?_, by norm_num, ?_⟩
  · simpa [PowerSeries.radius_eq_radius_ofScalars 𝕜] using hrad
  · intro q hq
    have hqn : ‖q‖ < 1 := by
      simpa using ENNReal.toReal_strict_mono (by simp) (mem_eball_zero_iff.mp hq)
    simpa [smul_eq_mul, mul_comm] using hasSum_eulerFunction_pentagonalSeries hqn

/-- The Euler function is analytic at zero. -/
theorem analyticAt_eulerFunction_zero : AnalyticAt 𝕜 (eulerFunction : 𝕜 → 𝕜) 0 :=
  hasFPowerSeriesOnBall_eulerFunction.analyticAt

/-- The Taylor series of the Euler function at zero is the pentagonal series. -/
theorem taylorSeries_eulerFunction :
    taylorSeries (eulerFunction : 𝕜 → 𝕜) 0 = pentagonalSeries 𝕜 := by
  ext n
  simpa using
    (hasFPowerSeriesOnBall_eulerFunction (𝕜 := 𝕜)).hasFPowerSeriesAt.coeff_taylorSeries n

end TauCeti
