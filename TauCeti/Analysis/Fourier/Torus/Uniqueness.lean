/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Decay
import TauCeti.MeasureTheory.Function.AEEqOfIntegralContinuous
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Uniqueness of Fourier coefficients on the torus

On the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` with its volume, the product of the Haar
probability measures of the circle factors, an integrable function `f` with values in a complex
Banach space is determined by its Fourier coefficients `mFourierCoeff f n = ∫ e_{-n} • f`.

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
* `TauCeti.UnitAddTorus.mFourierCoeff_sum_mFourier_smul`: the Fourier coefficients of a
  trigonometric polynomial.
* `MeasureTheory.Integrable.ae_eq_sum_mFourier_smul_mFourierCoeff`: an integrable function with
  finitely many nonzero Fourier coefficients is a trigonometric polynomial.
-/

public section

open MeasureTheory Set UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] {f g : UnitAddTorus d → E}

namespace TauCeti.UnitAddTorus

/-- The Fourier coefficients of a trigonometric polynomial `∑ n ∈ s, mFourier n • c n` are its
coefficients `c` on `s` and zero elsewhere. -/
@[simp]
theorem mFourierCoeff_sum_mFourier_smul (s : Finset (d → ℤ)) (c : (d → ℤ) → E) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ n ∈ s, mFourier n x • c n) m = if m ∈ s then c m else 0 := by
  have hmono (n : d → ℤ) : Integrable fun z : UnitAddTorus d ↦ mFourier (-m) z •
      (mFourier n z • c n) :=
    (by fun_prop : Continuous fun z : UnitAddTorus d ↦ mFourier (-m) z •
      (mFourier n z • c n)).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hcoeff (n : d → ℤ) : ∫ z, mFourier (-m) z • (mFourier n z • c n) =
      (Pi.single n 1 : (d → ℤ) → ℂ) m • c n := by
    rw [← mFourierCoeff_mFourier, mFourierCoeff_eq_integral_volume (mFourier n),
      ← integral_smul_const]
    simp_rw [smul_smul, smul_eq_mul]
  rw [mFourierCoeff_eq_integral_volume]
  simp only [Finset.smul_sum]
  rw [integral_finsetSum _ fun n _ ↦ hmono n]
  simp only [hcoeff]
  split_ifs with hm
  · rw [Finset.sum_eq_single m (fun n _ hn ↦ by simp [Ne.symm hn]) (fun h ↦ absurd hm h)]
    simp
  · refine Finset.sum_eq_zero fun n hn ↦ ?_
    have hnm : m ≠ n := fun h ↦ hm (h ▸ hn)
    simp [hnm]

end TauCeti.UnitAddTorus

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
  have hsmul {u : UnitAddTorus d → E} (hu : Integrable u) (n : d → ℤ) :
      Integrable fun z ↦ mFourier (-n) z • u z :=
    hu.bdd_smul 1 (mFourier (-n)).continuous.aestronglyMeasurable
      (ae_of_all _ fun z ↦ (norm_mFourier_apply (-n) z).le)
  have hfg := (hf.sub hg).ae_eq_zero_of_forall_mFourierCoeff_eq_zero fun n ↦ by
    have hn := h n
    rw [mFourierCoeff_eq_integral_volume, mFourierCoeff_eq_integral_volume] at hn
    simp only [mFourierCoeff_eq_integral_volume, Pi.sub_apply, smul_sub]
    rw [integral_sub (hsmul hf n) (hsmul hg n), hn, sub_self]
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
