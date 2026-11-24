/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import TauCeti.MeasureTheory.Measure.Haar.DistribChar

/-!
# The Fourier transform of a dilation by a unit

Let `𝕜` be a commutative topological ring and `V` a locally compact `𝕜`-module, with an additive
Haar measure `μ`, an additive character `e : AddChar 𝕜 𝕊` and a `𝕜`-bilinear pairing
`L : V × W → 𝕜`. For a unit `a ∈ 𝕜ˣ`, the Fourier transform of the dilated function
`v ↦ f (a • v)` is

`𝓕 (f (a • ·)) w = |a|_V⁻¹ • 𝓕 f (a⁻¹ • w)`,

where `|a|_V = MeasureTheory.distribHaarChar V a` is the factor by which `a` scales Haar measure
on `V` (`VectorFourier.fourierIntegral_comp_smul`). This only uses that `μ` is a Haar measure,
the substitution `v ↦ a • v`, and bilinearity of `L`; no normalization of `μ` is needed.

For a field `F` acting on itself with the multiplication pairing, this is the scaling law
`(r(a) f)^ = |a|⁻¹ r(a⁻¹) f̂` of Tate's thesis, where `r(a) f (x) = f (x a)` and `|a|` is the
module of `F` (`Fourier.fourierIntegral_comp_mul_right`). The module is the absolute value on
`ℝ` (`MeasureTheory.distribHaarChar_real_eq`), the square `a * conj a` of the absolute value on
`ℂ` (`MeasureTheory.distribHaarChar_complex_eq`) and the normalized absolute value on a
nonarchimedean local field (`MeasureTheory.distribHaarChar_eq_normalizedAbsoluteValue`), so the
law holds uniformly for every local field and every nontrivial additive character.

## Main results

* `VectorFourier.fourierIntegral_comp_smul`: the Fourier transform of `f (a • ·)`.
* `Fourier.fourierIntegral_comp_mul_right`: the Fourier transform of `f (· * a)` on a field.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.2.
* S. S. Kudla, *Tate's thesis*, in *An introduction to the Langlands program*, §2.
-/

public section

open MeasureTheory

variable {𝕜 : Type*} [CommRing 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [LocallyCompactSpace V] [ContinuousConstSMul 𝕜 V] [MeasurableSpace V]
  [BorelSpace V] {W : Type*} [AddCommGroup W] [Module 𝕜 W] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E]

namespace VectorFourier

/-- **Fourier transform of a dilation**: for a unit `a` of the scalar ring and an additive Haar
measure `μ`, `𝓕 (f (a • ·)) w = |a|_V⁻¹ • 𝓕 f (a⁻¹ • w)`, where `|a|_V = distribHaarChar V a` is
the factor by which `a` scales Haar measure. No integrability hypothesis is needed. -/
theorem fourierIntegral_comp_smul (e : AddChar 𝕜 Circle) (μ : Measure V) [μ.IsAddHaarMeasure]
    [μ.Regular] (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (a : 𝕜ˣ) (w : W) :
    fourierIntegral e μ L (fun v ↦ f (a • v)) w =
      ((distribHaarChar V a : ℝ))⁻¹ • fourierIntegral e μ L f (a⁻¹ • w) := by
  have hL (v : V) : L (a • v) (a⁻¹ • w) = L v w := by
    simp [Units.smul_def]
  unfold fourierIntegral
  rw [← integral_comp_smul_eq_inv_distribHaarChar_smul μ _ a]
  simp only [hL]

end VectorFourier

namespace Fourier

variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  [BorelSpace 𝕜]

/-- **Fourier transform of a dilation on a ring**: for a unit `a` and an additive Haar measure
`μ`, the transform of `r(a) f = f (· * a)` is `|a|⁻¹ • r(a⁻¹) 𝓕 f`, where
`|a| = distribHaarChar 𝕜 a` is the module of `a`. -/
theorem fourierIntegral_comp_mul_right (e : AddChar 𝕜 Circle) (μ : Measure 𝕜) [μ.IsAddHaarMeasure]
    [μ.Regular] (f : 𝕜 → E) (a : 𝕜ˣ) (w : 𝕜) :
    fourierIntegral e μ (fun x ↦ f (x * a)) w =
      ((distribHaarChar 𝕜 a : ℝ))⁻¹ • fourierIntegral e μ f (w * ↑a⁻¹) := by
  have h := VectorFourier.fourierIntegral_comp_smul e μ (LinearMap.mul 𝕜 𝕜) f a w
  simp only [Units.smul_def, smul_eq_mul, mul_comm (a : 𝕜), mul_comm (↑a⁻¹ : 𝕜)] at h
  exact h

end Fourier
