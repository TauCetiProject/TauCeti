/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Convolution with Fourier monomials on the torus

On the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` with its volume, the product of the Haar
probability measures of the circle factors, convolving with a monomial picks out one Fourier
coefficient,

`(mFourier n ⋆ f) x = ∫ mFourier n t • f (x - t) dt = mFourier n x • mFourierCoeff f n`,

because `mFourier n (x - t) = mFourier n x * mFourier (-n) t` and the volume is invariant under
`t ↦ x - t`.

## Main declarations

* `UnitAddTorus.convolution_mFourier_apply`: convolution with a monomial.
-/

public section

open MeasureTheory
open scoped Convolution

namespace UnitAddTorus

open TauCeti.UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Convolution with a Fourier monomial** picks out one Fourier coefficient:
`(mFourier n ⋆ f) x = mFourier n x • mFourierCoeff f n`. -/
theorem convolution_mFourier_apply (n : d → ℤ) (f : UnitAddTorus d → E) (x : UnitAddTorus d) :
    (⇑(mFourier n) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) x =
      mFourier n x • mFourierCoeff f n := by
  rw [convolution_def, mFourierCoeff_eq_integral_volume, ← integral_smul,
    ← integral_sub_left_eq_self _ volume x]
  congr 1 with t
  rw [ContinuousLinearMap.lsmul_apply, sub_sub_cancel, smul_smul, mFourier_apply_sub]

end UnitAddTorus
