/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Fourier.Continuous

/-!
# Uniqueness of the Fourier integral on integrable functions

The Fourier integral determines an integrable function almost everywhere. Fourier duality
reduces this to the uniqueness of a locally integrable function tested against smooth compactly
supported functions; no pointwise continuity of the input is required.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace MeasureTheory.Integrable

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : V → E}

/-- An integrable function with identically zero Fourier transform vanishes almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_zero (hf : Integrable f) (hF : 𝓕 f = 0) :
    f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgc
  have hgC : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let gS := (hgc.comp_left Complex.ofRealCLM.map_zero).toSchwartzMap hgC
  have hdual := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ V) Real.continuous_fourierChar continuous_inner
    ((𝓕⁻ gS).integrable (μ := volume)) hf
  have hpair : (∫ x, 𝓕 ((𝓕⁻ gS : SchwartzMap V ℂ) : V → ℂ) x • f x) =
      ∫ x, (𝓕⁻ gS : SchwartzMap V ℂ) x • 𝓕 f x := by
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, LinearMap.flip_apply,
      innerₗ_apply_apply, real_inner_comm] using hdual
  rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq, hF] at hpair
  simpa [gS, Complex.real_smul] using hpair

/-- Integrable functions with the same Fourier transform agree almost everywhere. -/
theorem ae_eq_of_fourier_eq {g : V → E} (hf : Integrable f) (hg : Integrable g)
    (hF : 𝓕 f = 𝓕 g) : f =ᵐ[volume] g := by
  have hsub : 𝓕 (f - g) = 0 := by rw [hf.fourier_sub hg, hF, sub_self]
  filter_upwards [(hf.sub hg).ae_eq_zero_of_fourier_eq_zero hsub] with x hx
  exact sub_eq_zero.mp hx

end MeasureTheory.Integrable
