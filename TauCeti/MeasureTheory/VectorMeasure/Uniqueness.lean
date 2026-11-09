/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import TauCeti.MeasureTheory.VectorMeasure.ScalarIntegral
public import TauCeti.MeasureTheory.VectorMeasure.Variation.Regular

/-!
# Scalar measures are determined by their integrals of continuous functions

Let `X` be a locally compact Hausdorff space with its Borel σ-algebra and let `𝕜` be `ℝ` or `ℂ`
(any `RCLike` field). A `𝕜`-valued measure `μ` on `X` whose variation `|μ|` is regular is
determined by the integrals `∫ f dμ` of the compactly supported continuous real functions `f`.
This is the uniqueness half of the Riesz representation theorem for the dual of `C₀(X, 𝕜)`; for
positive measures it is Mathlib's `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`.

On a compact space every continuous function is compactly supported, so a scalar measure of
regular variation on a compact Hausdorff space is determined by its integrals of the functions
in `C(X, 𝕜)`. This is how a measure is identified when only its action on continuous functions
is known, as for the polarized measures `B ↦ ⟪ξ, P(B) ψ⟫` attached to a representation of
`C(X, ℂ)` on a Hilbert space.

Regularity cannot be dropped: on a non-metrizable compact space there are distinct Borel
probability measures with the same integral for every continuous function. The variation of a
scalar measure is always finite (`MeasureTheory.VectorMeasure.isFiniteMeasure_variation`), so
regularity of `|μ|` is the only hypothesis.

## Main results

* `MeasureTheory.VectorMeasure.eq_zero_of_integral_eq_zero_on_compactlySupported`: a scalar
  measure of regular variation whose integral vanishes on `C_c(X, ℝ)` is zero.
* `MeasureTheory.VectorMeasure.ext_of_integral_eq_on_compactlySupported`: two scalar measures of
  regular variation with the same integrals on `C_c(X, ℝ)` are equal.
* `MeasureTheory.VectorMeasure.eq_zero_of_integral_eq_zero_on_continuousMap`,
  `MeasureTheory.VectorMeasure.ext_of_integral_eq_on_continuousMap`: the same on a compact
  space, tested against `C(X, 𝕜)`.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Theorem 6.19.
-/

public section

open MeasureTheory ContinuousLinearMap
open scoped CompactlySupported

namespace MeasureTheory.VectorMeasure

variable {X 𝕜 : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [RCLike 𝕜]

section LocallyCompact

variable [LocallyCompactSpace X]

/-- A signed measure of regular variation whose integral vanishes on `C_c(X, ℝ)` is zero. This is
the case `𝕜 = ℝ` of `eq_zero_of_integral_eq_zero_on_compactlySupported`, to which the general case
reduces through real and imaginary parts. -/
private theorem eq_zero_of_integral_eq_zero_on_compactlySupported_signed (σ : SignedMeasure X)
    [σ.variation.Regular] (h : ∀ f : C_c(X, ℝ), ∫ᵛ x, f x ∂[mul ℝ ℝ; σ] = 0) : σ = 0 := by
  -- The two parts of the Jordan decomposition are regular measures with the same integrals.
  set j := σ.toJordanDecomposition
  have hv : j.posPart + j.negPart = σ.variation := SignedMeasure.totalVariation_eq_variation σ
  have : j.posPart.Regular :=
    (Measure.absolutelyContinuous_of_le (hv ▸ Measure.le_add_right le_rfl)).regular
  have : j.negPart.Regular :=
    (Measure.absolutelyContinuous_of_le (hv ▸ Measure.le_add_left le_rfl)).regular
  have hj : j.posPart = j.negPart := Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ by
    rw [← sub_eq_zero, ← integral_mul_eq_integral_posPart_sub_integral_negPart σ f.integrable, h]
  calc σ = j.toSignedMeasure := σ.toSignedMeasure_toJordanDecomposition.symm
    _ = 0 := by simp [JordanDecomposition.toSignedMeasure, hj]

/-- **Uniqueness of scalar measures.** On a locally compact Hausdorff space, a scalar measure of
regular variation whose integral vanishes on every compactly supported continuous real function
is zero. -/
theorem eq_zero_of_integral_eq_zero_on_compactlySupported (μ : VectorMeasure X 𝕜)
    [μ.variation.Regular] (h : ∀ f : C_c(X, ℝ), ∫ᵛ x, (f x : 𝕜) ∂[mul ℝ 𝕜; μ] = 0) : μ = 0 := by
  have : (scalarMeasureRealPart μ).variation.Regular :=
    (Measure.absolutelyContinuous_of_le (variation_scalarMeasureRealPart_le μ)).regular
  have : (scalarMeasureImagPart μ).variation.Regular :=
    (Measure.absolutelyContinuous_of_le (variation_scalarMeasureImagPart_le μ)).regular
  have hre : scalarMeasureRealPart μ = 0 :=
    eq_zero_of_integral_eq_zero_on_compactlySupported_signed _ fun f ↦ by
      rw [← re_integral_ofReal f.integrable, h, _root_.map_zero]
  have him : scalarMeasureImagPart μ = 0 :=
    eq_zero_of_integral_eq_zero_on_compactlySupported_signed _ fun f ↦ by
      rw [← im_integral_ofReal f.integrable, h, _root_.map_zero]
  ext s
  rw [← scalarMeasureOfReal_realPart_add_I_smul_imagPart μ, hre, him]
  simp

/-- **Uniqueness of scalar measures.** On a locally compact Hausdorff space, two scalar measures
of regular variation with the same integral of every compactly supported continuous real function
are equal. -/
theorem ext_of_integral_eq_on_compactlySupported {μ ν : VectorMeasure X 𝕜} [μ.variation.Regular]
    [ν.variation.Regular]
    (h : ∀ f : C_c(X, ℝ), ∫ᵛ x, (f x : 𝕜) ∂[mul ℝ 𝕜; μ] = ∫ᵛ x, (f x : 𝕜) ∂[mul ℝ 𝕜; ν]) :
    μ = ν :=
  sub_eq_zero.1 <| eq_zero_of_integral_eq_zero_on_compactlySupported _ fun f ↦ by
    rw [integral_sub_vectorMeasure f.integrable.ofReal f.integrable.ofReal, h, sub_self]

end LocallyCompact

section Compact

variable [CompactSpace X]

/-- **Uniqueness of scalar measures.** On a compact Hausdorff space, a scalar measure of regular
variation whose integral vanishes on `C(X, 𝕜)` is zero. -/
theorem eq_zero_of_integral_eq_zero_on_continuousMap (μ : VectorMeasure X 𝕜)
    [μ.variation.Regular] (h : ∀ f : C(X, 𝕜), ∫ᵛ x, f x ∂[mul ℝ 𝕜; μ] = 0) : μ = 0 :=
  eq_zero_of_integral_eq_zero_on_compactlySupported μ fun f ↦
    h ⟨fun x ↦ (f x : 𝕜), RCLike.continuous_ofReal.comp f.continuous⟩

/-- **Uniqueness of scalar measures.** On a compact Hausdorff space, two scalar measures of regular
variation with the same integral of every function in `C(X, 𝕜)` are equal. -/
theorem ext_of_integral_eq_on_continuousMap {μ ν : VectorMeasure X 𝕜} [μ.variation.Regular]
    [ν.variation.Regular]
    (h : ∀ f : C(X, 𝕜), ∫ᵛ x, f x ∂[mul ℝ 𝕜; μ] = ∫ᵛ x, f x ∂[mul ℝ 𝕜; ν]) : μ = ν :=
  ext_of_integral_eq_on_compactlySupported fun f ↦
    h ⟨fun x ↦ (f x : 𝕜), RCLike.continuous_ofReal.comp f.continuous⟩

end Compact

end MeasureTheory.VectorMeasure
