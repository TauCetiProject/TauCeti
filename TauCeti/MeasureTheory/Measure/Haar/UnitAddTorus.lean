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

* `UnitAddTorus.volume_eq_pi_haarAddCircle`: the volume on the unit torus is the product of the
  Haar probability measures on its circle factors.
-/

public section

open MeasureTheory

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

end UnitAddTorus
