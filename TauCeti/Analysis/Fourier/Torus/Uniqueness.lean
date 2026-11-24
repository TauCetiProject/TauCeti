/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.MeasureTheory.Function.AEEqOfIntegralContinuous
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Uniqueness of Fourier coefficients on the torus

On the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` with its volume, the product of the Haar
probability measures of the circle factors, an integrable function `f` with values in a complex
Banach space is determined up to almost everywhere equality by its Fourier coefficients
`mFourierCoeff f n = ∫ e_{-n} • f`.

If all Fourier coefficients of `f` vanish, integration against `f` vanishes on the monomials
`mFourier n`, hence on every continuous function, because their span is uniformly dense
(`UnitAddTorus.span_mFourier_closure_eq_top` and
`MeasureTheory.Integrable.integral_smul_eq_zero_of_span_closure_eq_top`). This forces `f = 0`
almost everywhere (`MeasureTheory.Integrable.ae_eq_zero_of_forall_integral_smul_eq_zero`). This is
the multivariate form of `MeasureTheory.Integrable.ae_eq_zero_of_forall_fourierCoeff_eq_zero`. In
particular an integrable function whose Fourier coefficients vanish outside a finite set `s` is
almost everywhere the trigonometric polynomial `∑ n ∈ s, mFourier n • mFourierCoeff f n`.

## Main declarations

* `MeasureTheory.Integrable.ae_eq_zero_of_forall_mFourierCoeff_eq_zero`: uniqueness of Fourier
  coefficients for integrable functions.
* `MeasureTheory.Integrable.ae_eq_of_forall_mFourierCoeff_eq`: integrable functions with the same
  Fourier coefficients agree almost everywhere.
* `MeasureTheory.Integrable.ae_eq_sum_mFourier_smul_mFourierCoeff`: an integrable function with
  finitely many nonzero Fourier coefficients agrees almost everywhere with a trigonometric
  polynomial.
-/

public section

open MeasureTheory Set UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] {f g : UnitAddTorus d → E}

namespace MeasureTheory

open TauCeti.UnitAddTorus

/-- **Uniqueness of Fourier coefficients on the torus.** An integrable function on the torus whose
Fourier coefficients all vanish is zero almost everywhere. -/
theorem Integrable.ae_eq_zero_of_forall_mFourierCoeff_eq_zero (hf : Integrable f)
    (h : ∀ n, mFourierCoeff f n = 0) : f =ᵐ[volume] 0 :=
  hf.ae_eq_zero_of_forall_integral_smul_eq_zero fun φ ↦ by
    simpa [Complex.coe_smul] using hf.integral_smul_eq_zero_of_span_closure_eq_top
      span_mFourier_closure_eq_top (forall_mem_range.2 fun n ↦ by
        simpa [mFourierCoeff_eq_integral_volume] using h (-n))
      ⟨fun t ↦ (φ t : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩

/-- Integrable functions on the torus with the same Fourier coefficients agree almost
everywhere. -/
theorem Integrable.ae_eq_of_forall_mFourierCoeff_eq (hf : Integrable f) (hg : Integrable g)
    (h : ∀ n, mFourierCoeff f n = mFourierCoeff g n) : f =ᵐ[volume] g := by
  have hfg := (hf.sub hg).ae_eq_zero_of_forall_mFourierCoeff_eq_zero fun n ↦ by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ g, mFourierCoeff_add hf (hg.smul _), mFourierCoeff_smul,
      h n, neg_one_smul, add_neg_cancel]
  filter_upwards [hfg] with x hx
  simpa [sub_eq_zero] using hx

/-- An integrable function on the torus whose Fourier coefficients vanish outside a finite set `s`
is almost everywhere the trigonometric polynomial `∑ n ∈ s, mFourier n • mFourierCoeff f n`. -/
theorem Integrable.ae_eq_sum_mFourier_smul_mFourierCoeff (hf : Integrable f)
    {s : Finset (d → ℤ)} (hs : ∀ n ∉ s, mFourierCoeff f n = 0) :
    f =ᵐ[volume] fun x ↦ ∑ n ∈ s, mFourier n x • mFourierCoeff f n :=
  hf.ae_eq_of_forall_mFourierCoeff_eq ((by fun_prop : Continuous fun x ↦
    ∑ n ∈ s, mFourier n x • mFourierCoeff f n).integrable_of_hasCompactSupport
      (.of_compactSpace _)) fun m ↦ by
    rw [mFourierCoeff_sum_mFourier_smul]
    split_ifs with hm
    · rfl
    · exact hs m hm

end MeasureTheory
