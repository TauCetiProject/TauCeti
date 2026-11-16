/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.Fourier.Monomial

/-!
# Convolution with Fourier monomials on the torus

On the torus `𝕋ᵈ = UnitAddTorus d` with an invariant measure `μ`, such as its Haar probability
measure, convolving a function `f` with the Fourier monomial `e_n = mFourier n` keeps only the
`n`-th Fourier mode of `f`:

`(e_n ⋆ f)(x) = ∫ e_n(t) f(x - t) dμ(t) = e_n(x) ∫ e_{-n}(t) f(t) dμ(t)`

(`UnitAddTorus.mFourier_convolution`). For the Haar probability measure the last integral is the
Fourier coefficient `f̂(n)`. The proof substitutes `t ↦ x - t` and splits
`e_n(x - t) = e_n(x) e_{-n}(t)` (`UnitAddTorus.mFourier_apply_sub`). No integrability of `f` is
needed: where the integral defining `f̂(n)` diverges, both sides vanish.

By linearity, convolution with a trigonometric polynomial `∑ c_n e_n` is the Fourier multiplier
`f ↦ ∑ c_n f̂(n) e_n`. This is how convolution operators on `Lᵖ(𝕋ᵈ)` with trigonometric
polynomial kernels, such as the periodic Littlewood–Paley blocks, are identified with Fourier
multipliers.
-/

public section

open MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {μ : Measure (UnitAddTorus d)}

/-- A multivariate Fourier monomial turns a difference of points into a product:
`mFourier n (x - y) = mFourier n x * mFourier (-n) y`. -/
theorem mFourier_apply_sub (n : d → ℤ) (x y : UnitAddTorus d) :
    mFourier n (x - y) = mFourier n x * mFourier (-n) y := by
  have h1 := mFourier_apply_add n (x - y) y
  have h2 : mFourier (-n) y * mFourier n y = 1 := by
    rw [← mFourier_add, neg_add_cancel, mFourier_zero, ContinuousMap.one_apply]
  rw [sub_add_cancel] at h1
  linear_combination (-mFourier n (x - y)) * h2 - mFourier (-n) y * h1

/-- **Convolution with a Fourier monomial.** For an invariant measure `μ` on the torus, convolving
a function `f` with the monomial `mFourier n` keeps only its `n`-th Fourier mode:
`(mFourier n ⋆ f) x = mFourier n x • ∫ t, mFourier (-n) t • f t ∂μ`. For the Haar probability
measure the integral is the Fourier coefficient `mFourierCoeff f n`. -/
theorem mFourier_convolution [μ.IsAddLeftInvariant] [μ.IsNegInvariant] (n : d → ℤ)
    (f : UnitAddTorus d → E) :
    (mFourier n : UnitAddTorus d → ℂ) ⋆[lsmul ℂ ℂ, μ] f =
      fun x ↦ mFourier n x • ∫ t, mFourier (-n) t • f t ∂μ := by
  ext x
  rw [convolution_def, ← integral_smul, ← integral_sub_left_eq_self _ μ x]
  congr 1 with t
  rw [lsmul_apply, sub_sub_cancel, mFourier_apply_sub, smul_smul]

end UnitAddTorus
