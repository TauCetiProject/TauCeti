/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import TauCeti.MeasureTheory.VectorMeasure.Integral

/-!
# Integration against scalar measures

For an `RCLike` field `𝕜` and a `𝕜`-valued vector measure `μ` of finite variation, the integral
of a function `f : X → 𝕜` is Mathlib's vector-measure integral through the multiplication
pairing, `∫ᵛ x, f x ∂[mul ℝ 𝕜; μ]`. Mathlib proves its real-linearity in `f` and in `μ`. This
file supplies the remaining scalar calculus of this integral: homogeneity over `𝕜`, and the
reduction of a scalar measure to signed measures through its real and imaginary parts. These
are the comparisons needed to treat complex measures by the Jordan decomposition of their real
and imaginary parts, as in uniqueness theorems for measures on compact spaces.

The comparisons for the real and imaginary parts and the real-to-scalar embedding are instances
of the naturality of the vector-measure integral, `map_integral_comp_eq_integral_mapRangeL` in
`TauCeti.MeasureTheory.VectorMeasure.Integral`.

## Main declarations

* `MeasureTheory.VectorMeasure.integral_const_mul` and
  `MeasureTheory.VectorMeasure.integral_smul_vectorMeasure_mul`: `𝕜`-homogeneity of the scalar
  integral in the integrand and in the measure.
* `MeasureTheory.VectorMeasure.scalarMeasureRealPart`,
  `MeasureTheory.VectorMeasure.scalarMeasureImagPart`: the real and imaginary parts of a scalar
  measure, as real-linear maps to signed measures.
* `MeasureTheory.VectorMeasure.scalarMeasureOfReal`: a signed measure as a scalar measure.
* `MeasureTheory.VectorMeasure.scalarMeasureOfReal_realPart_add_I_smul_imagPart`: the
  reconstruction `μ = re μ + I • im μ`.
* `MeasureTheory.VectorMeasure.re_integral_ofReal`,
  `MeasureTheory.VectorMeasure.im_integral_ofReal`: the real and imaginary parts of the integral
  of a real function are its integrals against the real and imaginary parts of the measure.
* `MeasureTheory.VectorMeasure.integral_mul_eq_integral_posPart_sub_integral_negPart`: the
  integral against a signed measure through its Jordan decomposition.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill, 1987, Chapter 6.
-/

public section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X 𝕜 : Type*} [MeasurableSpace X]

section RCLike

variable [RCLike 𝕜]

/-- The integral against a scalar measure is `𝕜`-homogeneous in the integrand. -/
theorem integral_const_mul (μ : VectorMeasure X 𝕜) (c : 𝕜) (f : X → 𝕜) :
    ∫ᵛ x, c * f x ∂[mul ℝ 𝕜; μ] = c * ∫ᵛ x, f x ∂[mul ℝ 𝕜; μ] :=
  integral_fun_smul_of_smul_left (fun c x y => by simp [mul_assoc]) c f

/-- The integral against a scalar measure is `𝕜`-homogeneous in the measure. -/
@[simp]
theorem integral_smul_vectorMeasure_mul (μ : VectorMeasure X 𝕜) (c : 𝕜) (f : X → 𝕜) :
    ∫ᵛ x, f x ∂[mul ℝ 𝕜; c • μ] = c * ∫ᵛ x, f x ∂[mul ℝ 𝕜; μ] :=
  integral_smul_vectorMeasure_of_smul_right (fun c x y => by simp [mul_left_comm]) c f

/-- The real part of a scalar measure, as a signed measure. For `𝕜 = ℂ` this is
`MeasureTheory.ComplexMeasure.re` (`scalarMeasureRealPart_eq_re`). -/
noncomputable def scalarMeasureRealPart : VectorMeasure X 𝕜 →ₗ[ℝ] SignedMeasure X :=
  mapRangeL RCLike.reCLM

/-- The imaginary part of a scalar measure, as a signed measure. For `𝕜 = ℂ` this is
`MeasureTheory.ComplexMeasure.im` (`scalarMeasureImagPart_eq_im`). -/
noncomputable def scalarMeasureImagPart : VectorMeasure X 𝕜 →ₗ[ℝ] SignedMeasure X :=
  mapRangeL RCLike.imCLM

/-- A signed measure regarded as a scalar measure, through the embedding `ℝ → 𝕜`. -/
noncomputable def scalarMeasureOfReal : SignedMeasure X →ₗ[ℝ] VectorMeasure X 𝕜 :=
  mapRangeL RCLike.ofRealCLM

@[simp]
theorem scalarMeasureRealPart_apply (μ : VectorMeasure X 𝕜) (s : Set X) :
    scalarMeasureRealPart μ s = RCLike.re (μ s) :=
  (rfl)

@[simp]
theorem scalarMeasureImagPart_apply (μ : VectorMeasure X 𝕜) (s : Set X) :
    scalarMeasureImagPart μ s = RCLike.im (μ s) :=
  (rfl)

@[simp]
theorem scalarMeasureOfReal_apply (σ : SignedMeasure X) (s : Set X) :
    (scalarMeasureOfReal σ : VectorMeasure X 𝕜) s = σ s :=
  (rfl)

@[simp]
theorem scalarMeasureRealPart_scalarMeasureOfReal (σ : SignedMeasure X) :
    scalarMeasureRealPart (scalarMeasureOfReal σ : VectorMeasure X 𝕜) = σ := by
  ext s
  simp

@[simp]
theorem scalarMeasureImagPart_scalarMeasureOfReal (σ : SignedMeasure X) :
    scalarMeasureImagPart (scalarMeasureOfReal σ : VectorMeasure X 𝕜) = 0 := by
  ext s
  simp

/-- A scalar measure is recovered from its real and imaginary parts as `re μ + I • im μ`. -/
theorem scalarMeasureOfReal_realPart_add_I_smul_imagPart (μ : VectorMeasure X 𝕜) :
    scalarMeasureOfReal (scalarMeasureRealPart μ) +
      (RCLike.I : 𝕜) • scalarMeasureOfReal (scalarMeasureImagPart μ) = μ := by
  ext s
  simp [mul_comm RCLike.I, RCLike.re_add_im]

/-- For complex measures, `scalarMeasureRealPart` is Mathlib's `ComplexMeasure.re`. -/
theorem scalarMeasureRealPart_eq_re :
    (scalarMeasureRealPart : ComplexMeasure X →ₗ[ℝ] SignedMeasure X) = ComplexMeasure.re := by
  ext μ s
  rfl

/-- For complex measures, `scalarMeasureImagPart` is Mathlib's `ComplexMeasure.im`. -/
theorem scalarMeasureImagPart_eq_im :
    (scalarMeasureImagPart : ComplexMeasure X →ₗ[ℝ] SignedMeasure X) = ComplexMeasure.im := by
  ext μ s
  rfl

/-- The variation of the real part of a scalar measure is at most the variation of the
measure. -/
theorem variation_scalarMeasureRealPart_le (μ : VectorMeasure X 𝕜) :
    (scalarMeasureRealPart μ).variation ≤ μ.variation :=
  variation_le_of_forall_enorm_le fun s _ => (enorm_le_iff_norm_le.2
    (RCLike.norm_re_le_norm (μ s))).trans (enorm_measure_le_variation μ s)

/-- The variation of the imaginary part of a scalar measure is at most the variation of the
measure. -/
theorem variation_scalarMeasureImagPart_le (μ : VectorMeasure X 𝕜) :
    (scalarMeasureImagPart μ).variation ≤ μ.variation :=
  variation_le_of_forall_enorm_le fun s _ => (enorm_le_iff_norm_le.2
    (RCLike.norm_im_le_norm (μ s))).trans (enorm_measure_le_variation μ s)

/-- A signed measure and the scalar measure it defines have the same variation. -/
@[simp]
theorem variation_scalarMeasureOfReal (σ : SignedMeasure X) :
    (scalarMeasureOfReal σ : VectorMeasure X 𝕜).variation = σ.variation := by
  refine le_antisymm (variation_le_of_forall_enorm_le fun s _ => ?_) ?_
  · simpa [enorm_le_iff_norm_le] using enorm_measure_le_variation σ s
  · simpa using variation_scalarMeasureRealPart_le (scalarMeasureOfReal σ : VectorMeasure X 𝕜)

/-- A function integrable against a scalar measure is integrable against its real part. -/
theorem Integrable.scalarMeasureRealPart {V : Type*} [NormedAddCommGroup V]
    {μ : VectorMeasure X 𝕜} {f : X → V}
    (hf : μ.Integrable f) : (scalarMeasureRealPart μ).Integrable f :=
  MeasureTheory.Integrable.mono_measure hf (variation_scalarMeasureRealPart_le μ)

/-- A function integrable against a scalar measure is integrable against its imaginary part. -/
theorem Integrable.scalarMeasureImagPart {V : Type*} [NormedAddCommGroup V]
    {μ : VectorMeasure X 𝕜} {f : X → V}
    (hf : μ.Integrable f) : (scalarMeasureImagPart μ).Integrable f :=
  MeasureTheory.Integrable.mono_measure hf (variation_scalarMeasureImagPart_le μ)

/-- Integrability against a signed measure and against the scalar measure it defines agree. -/
@[simp]
theorem integrable_scalarMeasureOfReal_iff {V : Type*} [NormedAddCommGroup V]
    {σ : SignedMeasure X} {f : X → V} :
    (scalarMeasureOfReal σ : VectorMeasure X 𝕜).Integrable f ↔ σ.Integrable f := by
  simp [VectorMeasure.Integrable]

/-- The real part of the integral of a real function against a scalar measure is its integral
against the real part of the measure. -/
theorem re_integral_ofReal {μ : VectorMeasure X 𝕜} {f : X → ℝ} (hf : μ.Integrable f) :
    RCLike.re (∫ᵛ x, (f x : 𝕜) ∂[mul ℝ 𝕜; μ]) =
      ∫ᵛ x, f x ∂[mul ℝ ℝ; scalarMeasureRealPart μ] := by
  simpa [scalarMeasureRealPart] using map_integral_comp_eq_integral_mapRangeL μ hf
    (RCLike.ofRealCLM (K := 𝕜)) RCLike.reCLM RCLike.reCLM (B := mul ℝ 𝕜) (B' := mul ℝ ℝ)
    fun x y => by simp

/-- The imaginary part of the integral of a real function against a scalar measure is its
integral against the imaginary part of the measure. -/
theorem im_integral_ofReal {μ : VectorMeasure X 𝕜} {f : X → ℝ} (hf : μ.Integrable f) :
    RCLike.im (∫ᵛ x, (f x : 𝕜) ∂[mul ℝ 𝕜; μ]) =
      ∫ᵛ x, f x ∂[mul ℝ ℝ; scalarMeasureImagPart μ] := by
  simpa [scalarMeasureImagPart] using map_integral_comp_eq_integral_mapRangeL μ hf
    (RCLike.ofRealCLM (K := 𝕜)) RCLike.imCLM RCLike.imCLM (B := mul ℝ 𝕜) (B' := mul ℝ ℝ)
    fun x y => by simp

/-- Integrating a real function against a signed measure regarded as a scalar measure gives the
real integral. -/
theorem integral_ofReal_scalarMeasureOfReal {σ : SignedMeasure X} {f : X → ℝ}
    (hf : σ.Integrable f) :
    ∫ᵛ x, (f x : 𝕜) ∂[mul ℝ 𝕜; scalarMeasureOfReal σ] = ∫ᵛ x, f x ∂[mul ℝ ℝ; σ] := by
  have hf' : (scalarMeasureOfReal σ : VectorMeasure X 𝕜).Integrable f :=
    integrable_scalarMeasureOfReal_iff.2 hf
  refine RCLike.ext ?_ ?_
  · simp [re_integral_ofReal hf']
  · simp [im_integral_ofReal hf']

/-- A signed measure with a real density, regarded as a scalar measure, is the scalar measure
with the same density. -/
theorem scalarMeasureOfReal_withDensityᵥ {ν : Measure X} {r : X → ℝ} (hr : Integrable r ν) :
    (scalarMeasureOfReal (ν.withDensityᵥ r) : VectorMeasure X 𝕜) =
      ν.withDensityᵥ fun x => (r x : 𝕜) := by
  ext s hs
  simp [withDensityᵥ_apply hr hs, withDensityᵥ_apply (hr.ofReal (𝕜 := 𝕜)) hs, integral_ofReal]

end RCLike

section Signed

/-- Integrating a real function against a finite measure regarded as a signed measure, through the
multiplication pairing, gives its Bochner integral. -/
@[simp]
theorem integral_mul_toSignedMeasure {ν : Measure X} [IsFiniteMeasure ν] (f : X → ℝ) :
    ∫ᵛ x, f x ∂[mul ℝ ℝ; ν.toSignedMeasure] = ∫ x, f x ∂ν := by
  have hB : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = mul ℝ ℝ := by
    ext
    simp
  rw [← hB, integral_toSignedMeasure]

/-- Integrating against a difference of finite measures splits as a difference of Bochner
integrals. -/
theorem integral_mul_toSignedMeasure_sub {ν₁ ν₂ : Measure X} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] {f : X → ℝ} (h₁ : Integrable f ν₁) (h₂ : Integrable f ν₂) :
    ∫ᵛ x, f x ∂[mul ℝ ℝ; ν₁.toSignedMeasure - ν₂.toSignedMeasure] =
      ∫ x, f x ∂ν₁ - ∫ x, f x ∂ν₂ := by
  rw [integral_sub_vectorMeasure (by simpa [VectorMeasure.Integrable] using h₁)
    (by simpa [VectorMeasure.Integrable] using h₂), integral_mul_toSignedMeasure,
    integral_mul_toSignedMeasure]

/-- **Jordan split of the integral against a signed measure.** The integral of a function
integrable against the variation of `σ` is the difference of its Bochner integrals against the
positive and negative parts of the Jordan decomposition of `σ`. -/
theorem integral_mul_eq_integral_posPart_sub_integral_negPart (σ : SignedMeasure X)
    {f : X → ℝ} (hf : σ.Integrable f) :
    ∫ᵛ x, f x ∂[mul ℝ ℝ; σ] = ∫ x, f x ∂σ.toJordanDecomposition.posPart -
      ∫ x, f x ∂σ.toJordanDecomposition.negPart := by
  have hv : σ.variation = σ.toJordanDecomposition.posPart + σ.toJordanDecomposition.negPart :=
    (SignedMeasure.totalVariation_eq_variation σ).symm
  have hf' : Integrable f (σ.toJordanDecomposition.posPart + σ.toJordanDecomposition.negPart) :=
    hv ▸ hf
  conv_lhs => rw [← σ.toSignedMeasure_toJordanDecomposition]
  exact integral_mul_toSignedMeasure_sub hf'.left_of_add_measure hf'.right_of_add_measure

end Signed

end MeasureTheory.VectorMeasure
