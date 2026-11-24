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
import TauCeti.Analysis.Fourier.Torus.Uniqueness
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Convolution with trigonometric polynomials on the torus

On the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` with its volume, the product of the Haar
probability measures of the circle factors, convolving with a monomial picks out one Fourier
coefficient,

`(mFourier n ⋆ f) x = ∫ mFourier n t • f (x - t) dt = mFourier n x • mFourierCoeff f n`,

because `mFourier n (x - t) = mFourier n x * mFourier (-n) t` and the volume is invariant under
`t ↦ x - t`. So convolution with a trigonometric polynomial `∑ n ∈ s, c n * mFourier n` is the
Fourier multiplier whose symbol equals `c` on `s` and zero off `s`. By uniqueness of Fourier
coefficients, an integrable `g` with `ĝ = c • f̂` on `s` and `ĝ = 0` off `s` is almost everywhere
this convolution of `f`. This is how kernels of de la Vallée Poussin type reproduce functions whose
spectrum lies where their symbol equals one.

## Main declarations

* `UnitAddTorus.convolution_mFourier_apply`: convolution with a monomial.
* `MeasureTheory.Integrable.convolution_sum_mul_mFourier_apply`: convolution with a trigonometric
  polynomial.
* `MeasureTheory.Integrable.ae_eq_convolution_of_mFourierCoeff_eq_smul`: a function whose Fourier
  coefficients are those of `f` multiplied by `c` on a finite set `s` and vanish off `s` agrees
  almost everywhere with the convolution of `f` with the trigonometric polynomial
  `∑ n ∈ s, c n * mFourier n`.
-/

public section

open MeasureTheory Set
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

namespace MeasureTheory

open UnitAddTorus TauCeti.UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : UnitAddTorus d → E}

/-- **Convolution with a trigonometric polynomial** is the Fourier multiplier whose symbol is its
coefficient `c n` at each `n ∈ s` and zero off `s`: for integrable `f`,
`((∑ n ∈ s, c n * mFourier n) ⋆ f) x = ∑ n ∈ s, c n • mFourier n x • mFourierCoeff f n`. -/
theorem Integrable.convolution_sum_mul_mFourier_apply (hf : Integrable f) (s : Finset (d → ℤ))
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
  rw [MeasureTheory.integral_smul, ← convolution_mFourier_apply, convolution_def]
  simp

variable [CompleteSpace E]

/-- **Fourier multipliers with finitely supported symbols are convolutions.** If `f` and `g` are
integrable on the torus, the Fourier coefficients of `g` vanish outside a finite set `s` and
`ĝ(n) = c n • f̂(n)` on `s`, then `g` is almost everywhere the convolution of `f` with the
trigonometric polynomial `∑ n ∈ s, c n * mFourier n`. -/
theorem Integrable.ae_eq_convolution_of_mFourierCoeff_eq_smul (hg : Integrable g)
    (hf : Integrable f) {s : Finset (d → ℤ)} {c : (d → ℤ) → ℂ}
    (hgs : ∀ n ∉ s, mFourierCoeff g n = 0)
    (hfg : ∀ n ∈ s, mFourierCoeff g n = c n • mFourierCoeff f n) :
    g =ᵐ[volume]
      (fun t ↦ ∑ n ∈ s, c n * mFourier n t) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f := by
  filter_upwards [hg.ae_eq_sum_mFourier_smul_mFourierCoeff hgs] with x hx
  rw [hx, hf.convolution_sum_mul_mFourier_apply]
  exact Finset.sum_congr rfl fun n hn ↦ by rw [hfg n hn, smul_comm]

end MeasureTheory
