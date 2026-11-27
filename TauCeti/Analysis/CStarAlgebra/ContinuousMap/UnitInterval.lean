/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import TauCeti.MeasureTheory.Integral.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Typical functionals on `C([0,1])`

On the commutative C⋆-algebra `C(unitInterval, ℂ)` this file records the operator norm of
integration against Lebesgue measure on `[0,1]`. Weighted integrals against continuous nonnegative
weights are the general `ContinuousMap.weightedIntegral` applied to `volume` on the unit interval
(see `TauCeti.MeasureTheory.Integral.ContinuousMap`).

## Main declarations

* `ContinuousMap.unitIntervalVolumeIntegral`: integration against volume on the unit interval.
* `ContinuousMap.norm_unitIntervalVolumeIntegral`: its operator norm is `1`.
-/

public section

open scoped unitInterval ComplexOrder
open Filter MeasureTheory PositiveLinearMap

namespace ContinuousMap

/-! ### Integration against Lebesgue measure -/

/-- Integration against Lebesgue measure on the unit interval, as a positive continuous linear
functional. -/
noncomputable def unitIntervalVolumeIntegral : C(unitInterval, ℂ) →P[ℂ] ℂ :=
  (integralPositiveLinearMap (volume : Measure unitInterval)).toPositiveContinuousLinearMap

@[simp]
theorem unitIntervalVolumeIntegral_apply (f : C(unitInterval, ℂ)) :
    unitIntervalVolumeIntegral f = ∫ t, f t ∂(volume : Measure unitInterval) := by
  rw [unitIntervalVolumeIntegral, toPositiveContinuousLinearMap_apply,
    integralPositiveLinearMap_apply]

theorem unitIntervalVolumeIntegral_one :
    unitIntervalVolumeIntegral (1 : C(unitInterval, ℂ)) = 1 := by
  simp [unitIntervalVolumeIntegral_apply, ContinuousMap.one_apply, integral_const,
    Measure.real]

/-- Integration against volume on `[0,1]` has operator norm `1`. -/
theorem norm_unitIntervalVolumeIntegral :
    ‖unitIntervalVolumeIntegral.toContinuousLinearMap‖ = 1 := by
  have h := PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one unitIntervalVolumeIntegral
  -- `h` is the equality `(‖φ‖ : ℂ) = φ 1` in `ℂ`.
  simpa [unitIntervalVolumeIntegral_one, Complex.ofReal_eq_one] using
    (Complex.ofReal_re _).symm.trans (congrArg Complex.re h)

end ContinuousMap
