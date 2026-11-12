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
# Convolution with trigonometric polynomials on the torus

On the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` with its volume, the product of the Haar
probability measures of the circle factors, convolving with a monomial picks out one Fourier
coefficient,

`(mFourier n ⋆ f) x = ∫ mFourier n t • f (x - t) dt = mFourier n x • mFourierCoeff f n`,

because `mFourier n (x - t) = mFourier n x * mFourier (-n) t` and the volume is invariant under
`t ↦ x - t`. So convolution with a trigonometric polynomial `∑ n ∈ s, c n • mFourier n` is the
Fourier multiplier with the finitely supported symbol `c`. This is how kernels of de la Vallée
Poussin type reproduce functions whose spectrum lies where their symbol equals one.

## Main declarations

* `UnitAddTorus.convolution_mFourier_apply`: convolution with a monomial.
* `UnitAddTorus.convolution_sum_smul_mFourier_apply`: convolution with a trigonometric
  polynomial.
-/

public section

open MeasureTheory Set
open scoped Convolution

namespace UnitAddTorus

open TauCeti.UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : UnitAddTorus d → E}

/-- **Convolution with a Fourier monomial** picks out one Fourier coefficient:
`(mFourier n ⋆ f) x = mFourier n x • mFourierCoeff f n`. -/
theorem convolution_mFourier_apply (n : d → ℤ) (f : UnitAddTorus d → E) (x : UnitAddTorus d) :
    (⇑(mFourier n) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) x =
      mFourier n x • mFourierCoeff f n := by
  rw [convolution_def, mFourierCoeff_eq_integral_volume, ← integral_smul]
  rw [← integral_sub_left_eq_self _ volume x]
  congr 1 with t
  rw [ContinuousLinearMap.lsmul_apply, sub_sub_cancel, smul_smul, sub_eq_add_neg,
    mFourier_apply_add, mFourier_neg_apply]

/-- **Convolution with a trigonometric polynomial** is the Fourier multiplier with its finitely
supported coefficients: for integrable `f`,
`((∑ n ∈ s, c n • mFourier n) ⋆ f) x = ∑ n ∈ s, c n • mFourier n x • mFourierCoeff f n`. -/
theorem convolution_sum_smul_mFourier_apply (hf : Integrable f) (s : Finset (d → ℤ))
    (c : (d → ℤ) → ℂ) (x : UnitAddTorus d) :
    ((fun t ↦ ∑ n ∈ s, c n * mFourier n t) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) x =
      ∑ n ∈ s, c n • mFourier n x • mFourierCoeff f n := by
  have hint (n : d → ℤ) : Integrable fun t ↦ (c n * mFourier n t) • f (x - t) := by
    refine (hf.comp_sub_left x).bdd_smul ‖c n‖ (by fun_prop) (ae_of_all _ fun t ↦ ?_)
    simp [norm_mFourier_apply]
  simp_rw [convolution_def, ContinuousLinearMap.lsmul_apply, Finset.sum_smul]
  rw [integral_finsetSum _ fun n _ ↦ hint n]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp_rw [mul_smul]
  rw [integral_smul, ← convolution_mFourier_apply, convolution_def]
  simp

end UnitAddTorus
