/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.ScalarIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Radon–Nikodym densities and polar decomposition of scalar measures

For a scalar measure `μ` over an `RCLike` field and a sigma-finite positive measure `ν`,
absolute continuity of `μ.variation` with respect to `ν` gives an integrable density
`scalarRNDeriv μ ν`. It is assembled from the native signed Radon–Nikodym derivatives of
the real and imaginary parts and agrees with the native derivatives over `ℝ` and `ℂ`.

The variation has density `‖scalarRNDeriv μ ν‖ₑ`. In particular, relative to its own
variation every scalar measure has a density of norm one almost everywhere. This polar
decomposition supplies the phase used to recover total variation from integration pairings.
No topology or regularity assumption on the underlying measurable space is needed.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Chapter 6, Radon–Nikodym theorem
  and polar decomposition of a complex measure.

The construction uses Mathlib's `SignedMeasure.rnDeriv`,
`SignedMeasure.withDensityᵥ_rnDeriv_eq`, and `Measure.variation_withDensityᵥ`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.SignedMeasure

variable {X : Type*} [MeasurableSpace X]

/-- A signed measure is reconstructed by its Radon–Nikodym density when its variation is
absolutely continuous with respect to the sigma-finite reference measure. -/
theorem withDensityᵥ_rnDeriv_eq_of_variation (s : SignedMeasure X) (ν : Measure X)
    [SigmaFinite ν] (h : s.variation ≪ ν) : ν.withDensityᵥ (s.rnDeriv ν) = s := by
  apply withDensityᵥ_rnDeriv_eq
  rwa [absolutelyContinuous_ennreal_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure, totalVariation_eq_variation]

end MeasureTheory.SignedMeasure

namespace MeasureTheory.VectorMeasure

variable {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]

/-- The scalar Radon–Nikodym density, formed from the signed derivatives of the real and
imaginary parts. It reconstructs the measure when its variation is absolutely continuous
with respect to the sigma-finite reference measure. -/
noncomputable def scalarRNDeriv (μ : VectorMeasure X 𝕜) (ν : Measure X) : X → 𝕜 :=
  fun x ↦ ((scalarMeasureRealPart μ).rnDeriv ν x : 𝕜) +
    RCLike.I * ((scalarMeasureImagPart μ).rnDeriv ν x : 𝕜)

/-- Formula for the scalar density in terms of native signed derivatives. -/
theorem scalarRNDeriv_def (μ : VectorMeasure X 𝕜) (ν : Measure X) :
    scalarRNDeriv μ ν = fun x ↦ ((scalarMeasureRealPart μ).rnDeriv ν x : 𝕜) +
      RCLike.I * ((scalarMeasureImagPart μ).rnDeriv ν x : 𝕜) :=
  (rfl)

/-- The scalar Radon–Nikodym density is measurable. -/
@[fun_prop]
theorem measurable_scalarRNDeriv [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : VectorMeasure X 𝕜) (ν : Measure X) :
    Measurable (scalarRNDeriv μ ν) := by
  rw [scalarRNDeriv_def]
  have hcont : Continuous (fun p : ℝ × ℝ ↦ (p.1 : 𝕜) + RCLike.I * (p.2 : 𝕜)) := by
    fun_prop
  exact hcont.measurable.comp ((SignedMeasure.measurable_rnDeriv _ _).prodMk
    (SignedMeasure.measurable_rnDeriv _ _))

/-- The scalar Radon–Nikodym density is integrable, even without absolute continuity. -/
theorem integrable_scalarRNDeriv (μ : VectorMeasure X 𝕜) (ν : Measure X) :
    Integrable (scalarRNDeriv μ ν) ν := by
  rw [scalarRNDeriv_def]
  exact (SignedMeasure.integrable_rnDeriv _ _).ofReal.add
    ((SignedMeasure.integrable_rnDeriv _ _).ofReal.const_mul _)

/-- Over the real field, the scalar density is the native signed density. -/
@[simp]
theorem scalarRNDeriv_real (μ : SignedMeasure X) (ν : Measure X) :
    scalarRNDeriv μ ν = μ.rnDeriv ν := by
  have hre : scalarMeasureRealPart μ = μ := by ext s; simp
  simp [scalarRNDeriv_def, hre]

/-- Over the complex field, the scalar density is the native complex density. -/
@[simp]
theorem scalarRNDeriv_complex (μ : ComplexMeasure X) (ν : Measure X) :
    scalarRNDeriv μ ν = μ.rnDeriv ν := by
  ext x
  simp [scalarRNDeriv_def, scalarMeasureRealPart_eq_re, scalarMeasureImagPart_eq_im,
    ComplexMeasure.rnDeriv, Complex.ext_iff]

/-- **Scalar Radon–Nikodym theorem.** If the variation of a scalar measure is absolutely
continuous with respect to a sigma-finite measure, its scalar density reconstructs it. -/
theorem withDensityᵥ_scalarRNDeriv (μ : VectorMeasure X 𝕜) (ν : Measure X) [SigmaFinite ν]
    (hμν : μ.variation ≪ ν) : ν.withDensityᵥ (scalarRNDeriv μ ν) = μ := by
  have hre := SignedMeasure.withDensityᵥ_rnDeriv_eq_of_variation (scalarMeasureRealPart μ) ν
    ((Measure.absolutelyContinuous_of_le (variation_scalarMeasureRealPart_le μ)).trans hμν)
  have him := SignedMeasure.withDensityᵥ_rnDeriv_eq_of_variation (scalarMeasureImagPart μ) ν
    ((Measure.absolutelyContinuous_of_le (variation_scalarMeasureImagPart_le μ)).trans hμν)
  have hreal := SignedMeasure.integrable_rnDeriv (scalarMeasureRealPart μ) ν
  have himag := SignedMeasure.integrable_rnDeriv (scalarMeasureImagPart μ) ν
  calc
    _ = ν.withDensityᵥ (fun x ↦ ((scalarMeasureRealPart μ).rnDeriv ν x : 𝕜)) +
        RCLike.I • ν.withDensityᵥ (fun x ↦ ((scalarMeasureImagPart μ).rnDeriv ν x : 𝕜)) := by
      rw [scalarRNDeriv_def, withDensityᵥ_add' hreal.ofReal (himag.ofReal.const_mul _)]
      congr 1
      exact withDensityᵥ_smul' (μ := ν)
        (fun x ↦ ((scalarMeasureImagPart μ).rnDeriv ν x : 𝕜)) (RCLike.I : 𝕜)
    _ = μ := by
      rw [← scalarMeasureOfReal_withDensityᵥ hreal, ← scalarMeasureOfReal_withDensityᵥ himag,
        hre, him, scalarMeasureOfReal_realPart_add_I_smul_imagPart]

/-- The variation of a scalar measure is obtained by taking the pointwise norm of its
Radon–Nikodym density. -/
theorem variation_eq_withDensity_enorm_scalarRNDeriv (μ : VectorMeasure X 𝕜) (ν : Measure X)
    [SigmaFinite ν] (hμν : μ.variation ≪ ν) :
    μ.variation = ν.withDensity (fun x ↦ ‖scalarRNDeriv μ ν x‖ₑ) := by
  rw [← Measure.variation_withDensityᵥ (integrable_scalarRNDeriv μ ν),
    withDensityᵥ_scalarRNDeriv μ ν hμν]

/-- An integrable function represents a scalar measure exactly when it agrees almost
everywhere with its scalar Radon–Nikodym density. -/
theorem withDensityᵥ_eq_iff_ae_eq_scalarRNDeriv (μ : VectorMeasure X 𝕜) (ν : Measure X)
    [SigmaFinite ν] (hμν : μ.variation ≪ ν) {f : X → 𝕜} (hf : Integrable f ν) :
    ν.withDensityᵥ f = μ ↔ f =ᵐ[ν] scalarRNDeriv μ ν := by
  simpa only [withDensityᵥ_scalarRNDeriv μ ν hμν] using
    hf.withDensityᵥ_eq_iff (integrable_scalarRNDeriv μ ν)

/-- The density of a scalar measure relative to its own variation has norm one almost
everywhere. This includes the zero measure, whose almost-everywhere assertion is vacuous. -/
theorem ae_norm_scalarRNDeriv_variation_eq_one (μ : VectorMeasure X 𝕜) :
    ∀ᵐ x ∂μ.variation, ‖scalarRNDeriv μ μ.variation x‖ = 1 := by
  have h := variation_eq_withDensity_enorm_scalarRNDeriv μ μ.variation
    Measure.AbsolutelyContinuous.rfl
  have hd : μ.variation.withDensity (fun x ↦ ‖scalarRNDeriv μ μ.variation x‖ₑ) =
      μ.variation.withDensity (fun _ ↦ 1) := by simpa using h.symm
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (integrable_scalarRNDeriv μ μ.variation).aestronglyMeasurable.enorm
    measurable_const.aemeasurable).1 hd
  filter_upwards [hae] with x hx
  simpa using congrArg ENNReal.toReal hx

end MeasureTheory.VectorMeasure
