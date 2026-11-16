/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.Fourier.Monomial

/-!
# Convolution on the torus

On the torus `𝕋ᵈ = UnitAddTorus d` with an invariant measure `μ`, such as its Haar probability
measure, convolving a function `f` with the Fourier monomial `e_n = mFourier n` keeps only the
`n`-th Fourier mode of `f`:

`(e_n ⋆ f)(x) = ∫ e_n(t) f(x - t) dμ(t) = e_n(x) ∫ e_{-n}(t) f(t) dμ(t)`

(`UnitAddTorus.mFourier_convolution`). For the Haar probability measure the last integral is the
Fourier coefficient `f̂(n)`. The proof substitutes `t ↦ x - t` and splits
`e_n(x - t) = e_n(x) e_{-n}(t)` (`UnitAddTorus.mFourier_apply_sub`). No integrability of `f` is
needed: where the integral defining `f̂(n)` diverges, both sides vanish.

By linearity, convolution of an integrable `f` with a trigonometric polynomial `∑ c_n e_n` is the
Fourier multiplier `f ↦ ∑ c_n f̂(n) e_n` (`UnitAddTorus.sum_mul_mFourier_convolution`). This is
how convolution operators on `Lᵖ(𝕋ᵈ)` with trigonometric polynomial kernels, such as the periodic
Littlewood–Paley blocks (`ContinuousMap.convolutionLp`), are identified with Fourier multipliers.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {μ : Measure (UnitAddTorus d)}

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

/-- **Convolution with a trigonometric polynomial.** For an invariant measure `μ` on the torus and
an integrable `f`, convolving `f` with the trigonometric polynomial `∑ n ∈ s, c n e_n` multiplies
its Fourier modes by `c n`:
`(∑ n ∈ s, c n e_n) ⋆ f = ∑ n ∈ s, c n e_n • ∫ t, mFourier (-n) t • f t ∂μ`. -/
theorem sum_mul_mFourier_convolution [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) {f : UnitAddTorus d → E} (hf : Integrable f μ) :
    (fun t ↦ ∑ n ∈ s, c n * mFourier n t) ⋆[lsmul ℂ ℂ, μ] f =
      fun x ↦ ∑ n ∈ s, (c n * mFourier n x) • ∫ t, mFourier (-n) t • f t ∂μ := by
  ext x
  rw [convolution_def]
  simp_rw [lsmul_apply, Finset.sum_smul]
  rw [integral_finsetSum _ fun n _ ↦ ?_]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    have h := congr_fun (mFourier_convolution (μ := μ) n f) x
    simp only [convolution_def, lsmul_apply] at h
    simp_rw [mul_smul, integral_smul, h]
  · exact (hf.comp_sub_left x).bdd_smul ‖c n‖
      (by fun_prop : Continuous fun t ↦ c n * mFourier n t).aestronglyMeasurable
      (.of_forall fun t ↦ by simp)

end UnitAddTorus
