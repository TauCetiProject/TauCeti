/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# The volume on the unit torus

Mathlib states its results on Fourier series on the unit torus `UnitAddTorus d = (ℝ / ℤ)^d`, such
as `UnitAddTorus.orthonormal_mFourier` and the definition of `UnitAddTorus.mFourierCoeff`, for a
file-local measure: the product of the Haar probability measures `AddCircle.haarAddCircle` on the
circle factors. This file records that this product is the global `volume` on the torus, so that
those results can be read for `volume`.

## Main results

* An instance stating that the volume on the unit circle `UnitAddCircle` is a probability measure.
* `TauCeti.UnitAddTorus.volume_eq_pi_haarAddCircle`: the volume on the unit torus is the product of
  the Haar probability measures on its circle factors.
* `TauCeti.UnitAddTorus.mFourierCoeff_eq_integral_volume`: the Fourier coefficients on the unit
  torus are integrals for the volume.
-/

public section

open MeasureTheory UnitAddTorus

namespace TauCeti

/-- The volume on the unit circle `ℝ / ℤ` is a probability measure. -/
instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The volume on the unit torus is the product of the Haar probability measures on its circle
factors. -/
theorem volume_eq_pi_haarAddCircle :
    (volume : Measure (UnitAddTorus d)) = Measure.pi fun _ ↦ AddCircle.haarAddCircle := by
  rw [volume_pi]
  congr 1
  funext
  simp [AddCircle.volume_eq_smul_haarAddCircle]

/-- The Fourier coefficients of `f` are integrals for the volume of the torus. Mathlib defines
`mFourierCoeff` using the Haar probability measure on each circle factor; this is the volume. -/
theorem mFourierCoeff_eq_integral_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : UnitAddTorus d → E) (n : d → ℤ) :
    mFourierCoeff f n = ∫ z, mFourier (-n) z • f z := by
  rw [volume_eq_pi_haarAddCircle]
  -- Mathlib defines `mFourierCoeff` with its file-local normalization
  -- `volume = haarAddCircle` on `UnitAddCircle`, whose product measure is the measure above.
  rfl

end UnitAddTorus

end TauCeti
