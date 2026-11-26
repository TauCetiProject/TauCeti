/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.Analysis.Analytic.TaylorSeries
import TauCeti.Analysis.Analytic.PowerSubstitution
import TauCeti.Combinatorics.Enumerative.Pentagonal.PowerSeries
import TauCeti.RingTheory.PowerSeries.Radius

/-!
# The Taylor series of the Euler function

The pentagonal series gives the analytic expansion of the Euler function on the open unit ball,
allowing Euler products to be compared with formal power series over other coefficient rings.
Positive power substitution expands every exponent of this series by the same factor.

## Main results

* `TauCeti.analyticAt_eulerFunction_comp_pow`: every natural power substitution is analytic
  at zero, including the constant substitution with exponent zero.
* `TauCeti.taylorSeries_eulerFunction`: the Euler function has the pentagonal Taylor series.
* `TauCeti.taylorSeries_eulerFunction_comp_pow`: positive power substitution expands the
  pentagonal Taylor series.
-/

public section

open PowerSeries

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

/-- The Euler function composed with any natural power is analytic at zero. For exponent zero,
the composition is constant. -/
theorem analyticAt_eulerFunction_comp_pow (k : ℕ) :
    AnalyticAt 𝕜 (fun q : 𝕜 ↦ eulerFunction (q ^ k)) 0 := by
  by_cases hk : k = 0
  · simpa [hk] using
      (analyticAt_const : AnalyticAt 𝕜 (fun _ : 𝕜 ↦ eulerFunction (1 : 𝕜)) 0)
  · exact analyticAt_eulerFunction_zero.comp_of_eq (by fun_prop) (zero_pow hk)

/-- The Taylor series of the Euler function at zero is the pentagonal series. -/
@[simp]
theorem taylorSeries_eulerFunction :
    taylorSeries (eulerFunction : 𝕜 → 𝕜) 0 = pentagonalSeries 𝕜 := by
  ext n
  simpa using
    (hasFPowerSeriesOnBall_eulerFunction (𝕜 := 𝕜)).hasFPowerSeriesAt.coeff_taylorSeries n

/-- The Taylor series of the Euler function after a positive power substitution is obtained by
expanding the exponents of the pentagonal series by the same factor. -/
@[simp]
theorem taylorSeries_eulerFunction_comp_pow (k : ℕ) (hk : k ≠ 0) :
    taylorSeries (fun q : 𝕜 ↦ eulerFunction (q ^ k)) 0 =
      PowerSeries.expand k hk (pentagonalSeries 𝕜) := by
  rw [taylorSeries_comp_pow analyticAt_eulerFunction_zero k hk, taylorSeries_eulerFunction]

end TauCeti
