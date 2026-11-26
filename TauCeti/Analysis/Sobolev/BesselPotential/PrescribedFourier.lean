/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Elements of `H^s` with a prescribed Fourier transform

Let `E` be a finite-dimensional real inner product space. A tempered distribution `u` lies in the
Bessel-potential space `H^s` when `⟨η⟩ ^ s 𝓕 u`, for `⟨η⟩ = (1 + ‖η‖ ^ 2) ^ (1 / 2)`, is an `L²`
function. Conversely, every function `F` with `⟨η⟩ ^ s F` square integrable is the Fourier
transform of an element of `H^s`: the inverse Fourier transform of `⟨η⟩ ^ (-s)` times the `L²`
function `⟨η⟩ ^ s F`.

## Main declarations

* `TemperedDistribution.smulLeftCLM_one_add_norm_sq_rpow_neg_toLp_apply`: multiplying the `L²`
  function `⟨η⟩ ^ s F` by `⟨η⟩ ^ (-s)` gives back the function `F`.
* `TemperedDistribution.exists_memSobolev_fourier_apply_eq_integral`: a function `F` with
  `⟨η⟩ ^ s F` square integrable is the Fourier transform of an element of `H^s`.
-/

public section

noncomputable section

open Complex MeasureTheory
open scoped SchwartzMap FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

/-- **Pairing a weighted `L²` function with the weight `⟨η⟩ ^ (-s)`.** If
`⟨η⟩ ^ s F = (1 + ‖η‖ ^ 2) ^ (s / 2) F` is square integrable, then multiplying this `L²` function,
viewed as a tempered distribution, by `⟨η⟩ ^ (-s)` gives the function `F`:
`g ↦ ∫ g η • F η`. -/
theorem smulLeftCLM_one_add_norm_sq_rpow_neg_toLp_apply {s : ℝ} {F : E → ℂ}
    (hF : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η) 2 volume) (g : 𝓢(E, ℂ)) :
    smulLeftCLM ℂ (fun η : E ↦ (((1 + ‖η‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ))
      (hF.toLp _ : 𝓢'(E, ℂ)) g = ∫ η, g η • F η := by
  have hw : (fun η : E ↦ (((1 + ‖η‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  rw [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae (hF.coeFn_toLp.mono fun η hη ↦ ?_)
  dsimp only at hη ⊢
  rw [hη, SchwartzMap.smulLeftCLM_apply_apply hw]
  have hpos : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have hne : (((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.rpow_pos_of_pos hpos _).ne'
  simp only [neg_div, Real.rpow_neg hpos.le, smul_eq_mul, Complex.real_smul, ofReal_inv]
  field_simp

/-- **An element of `H^s` with a prescribed Fourier transform.** If `F` is a function with
`⟨η⟩ ^ s F = (1 + ‖η‖ ^ 2) ^ (s / 2) F` square integrable, then some element `u` of the
Bessel-potential space `H^s` has Fourier transform the function `F`: `𝓕 u g = ∫ g η • F η` for
every Schwartz function `g`. -/
theorem exists_memSobolev_fourier_apply_eq_integral {s : ℝ} {F : E → ℂ}
    (hF : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η) 2 volume) :
    ∃ u : 𝓢'(E, ℂ), MemSobolev s 2 u ∧ ∀ g : 𝓢(E, ℂ), 𝓕 u g = ∫ η, g η • F η := by
  -- `u` is the inverse Fourier transform of `⟨η⟩ ^ (-s)` times the `L²` function `⟨η⟩ ^ s F`.
  set w : E → ℂ := fun η ↦ (((1 + ‖η‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := by fun_prop
  have hb : (fun η : E ↦ (((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hwb : (w * fun η : E ↦ (((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) = fun _ ↦ 1 := by
    funext η
    simp only [w, Pi.mul_apply]
    rw [← ofReal_mul, TauCeti.one_add_norm_sq_rpow_neg_mul_rpow, ofReal_one]
  set v : 𝓢'(E, ℂ) := smulLeftCLM ℂ w (hF.toLp _ : 𝓢'(E, ℂ))
  have hv : 𝓕 (𝓕⁻ v) = v := FourierTransform.fourier_fourierInv_eq v
  refine ⟨𝓕⁻ v, memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨hF.toLp _, ?_⟩, fun g ↦ ?_⟩
  · rw [hv, smulLeftCLM_smulLeftCLM_apply hw hb, hwb, smulLeftCLM_const, one_smul]
  · rw [hv]
    exact smulLeftCLM_one_add_norm_sq_rpow_neg_toLp_apply hF g

end TemperedDistribution
