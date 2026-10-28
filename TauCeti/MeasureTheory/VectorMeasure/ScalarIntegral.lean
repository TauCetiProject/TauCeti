/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.SetToL1.ChangeMeasure
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Integration against scalar measures

For an `RCLike` field `𝕜` and a `𝕜`-valued vector measure `μ` of finite variation, the integral
of a function `f : X → 𝕜` is Mathlib's vector-measure integral through the multiplication
pairing, `∫ᵛ x, f x ∂[mul ℝ 𝕜; μ]`. Mathlib proves its real-linearity in `f` and in `μ`. This
file supplies the remaining scalar calculus of this integral: homogeneity over `𝕜`, and the
reduction of a scalar measure to signed measures through its real and imaginary parts. These
are the comparisons needed to treat complex measures by the Jordan decomposition of their real
and imaginary parts, as in uniqueness theorems for measures on compact spaces.

The integral is natural in the measure: a continuous linear map `φ` applied to the values of `μ`
corresponds to a continuous linear map applied to the integral, whenever the pairings are
compatible (`map_integral_comp_eq_integral_mapRangeL`). The real and imaginary parts and the
real-to-scalar embedding are instances of this naturality.

## Main declarations

* `MeasureTheory.VectorMeasure.map_integral_comp_eq_integral_mapRangeL`: naturality of the
  vector-measure integral under continuous linear maps of the values.
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

section mapRangeL

variable {α M N R : Type*} [MeasurableSpace α] [Semiring R]
  [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [TopologicalSpace N] [AddCommMonoid N] [Module R N] [ContinuousAdd N] [ContinuousConstSMul R N]

@[simp]
theorem mapRangeL_apply (f : M →L[R] N) (v : VectorMeasure α M) (s : Set α) :
    mapRangeL f v s = f (v s) :=
  rfl

end mapRangeL

variable {X E₀ E F F' G G' 𝕜 : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']

/-- Applying a continuous linear map to the values of a vector measure multiplies its variation
by at most the operator norm of the map. -/
theorem variation_mapRangeL_le (φ : F →L[ℝ] F') (μ : VectorMeasure X F) :
    (mapRangeL φ μ).variation ≤ ‖φ‖₊ • μ.variation := by
  refine variation_le_of_forall_enorm_le fun s _ => ?_
  rw [mapRangeL_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  refine (φ.le_opENorm _).trans ?_
  rw [enorm_eq_nnnorm φ]
  gcongr
  exact enorm_measure_le_variation μ s

/-- **Naturality of the vector-measure integral.** Let `ψ`, `φ` and `L` be continuous linear maps
on the integrand, on the values of the measure and on the values of the integral, compatible with
the pairings `B` and `B'` in the sense that `L (B (ψ x) y) = B' x (φ y)`. Then for `f` integrable
against `μ`, applying `L` to the integral of `ψ ∘ f` against `μ` gives the integral of `f` against
the measure `φ ∘ μ`. -/
theorem map_integral_comp_eq_integral_mapRangeL [CompleteSpace G] [CompleteSpace G']
    (μ : VectorMeasure X F) {f : X → E₀} (hf : μ.Integrable f) (ψ : E₀ →L[ℝ] E)
    (φ : F →L[ℝ] F') (L : G →L[ℝ] G') {B : E →L[ℝ] F →L[ℝ] G} {B' : E₀ →L[ℝ] F' →L[ℝ] G'}
    (h : ∀ x y, L (B (ψ x) y) = B' x (φ y)) :
    L (∫ᵛ x, ψ (f x) ∂[B; μ]) = ∫ᵛ x, f x ∂[B'; mapRangeL φ μ] := by
  have hvar := variation_mapRangeL_le φ μ
  rw [ENNReal.smul_def] at hvar
  have hc : ((‖φ‖₊ : ℝ≥0) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hint : ∀ g : X → E₀, μ.Integrable g → (mapRangeL φ μ).Integrable g :=
    fun g hg => hg.of_measure_le_smul hc hvar
  -- Induction on integrable functions, following Mathlib's
  -- `MeasureTheory.setToFun_congr_measure_of_integrable`.
  refine hf.induction
    (P := fun f => L (∫ᵛ x, ψ (f x) ∂[B; μ]) = ∫ᵛ x, f x ∂[B'; mapRangeL φ μ]) ?_ ?_ ?_ ?_
  · intro c s hs hμs
    have : IsFiniteMeasure (μ.variation.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
    have : IsFiniteMeasure ((mapRangeL φ μ).variation.restrict s) :=
      isFiniteMeasure_restrict.2 ((hvar s).trans_lt (by
        simpa using ENNReal.mul_lt_top ENNReal.coe_lt_top hμs)).ne
    have hψ : (fun x => ψ (s.indicator (fun _ => c) x)) = s.indicator fun _ => ψ c := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hψ, integral_indicator_const _ hs, integral_indicator_const _ hs, h, mapRangeL_apply]
  · intro f g _ hf hg hf' hg'
    have hψ : (fun x => ψ ((f + g) x)) = fun x => ψ (f x) + ψ (g x) := by
      ext x
      simp
    rw [hψ, integral_fun_add (ψ.integrable_comp hf) (ψ.integrable_comp hg), L.map_add,
      integral_add (hint f hf) (hint g hg), hf', hg']
  · have hL : (fun g : X →₁[μ.variation] E₀ => L (∫ᵛ x, ψ (g x) ∂[B; μ])) =
        fun g => L (∫ᵛ x, (ψ.compLpL 1 μ.variation g) x ∂[B; μ]) := by
      ext1 g
      rw [integral_congr_ae (ψ.coeFn_compLpL g).symm]
    have hR : (fun g : X →₁[μ.variation] E₀ => ∫ᵛ x, g x ∂[B'; mapRangeL φ μ]) =
        fun g : X →₁[μ.variation] E₀ =>
          ∫ᵛ x, ((hint g (L1.integrable_coeFn g)).toL1 g) x ∂[B'; mapRangeL φ μ] := by
      ext1 g
      exact integral_congr_ae (Integrable.coeFn_toL1 _).symm
    refine isClosed_eq ?_ ?_
    · rw [hL]
      exact L.continuous.comp (continuous_integral.comp (ψ.compLpL 1 μ.variation).continuous)
    · rw [hR]
      exact continuous_integral.comp (continuous_L1_toL1 _ hc hvar)
  · intro f g hfg _ hf'
    have hfg' : f =ᵐ[(mapRangeL φ μ).variation] g :=
      (Measure.absolutelyContinuous_of_le_smul hvar).ae_eq hfg
    rw [← integral_congr_ae (hfg.mono fun x hx => congrArg ψ hx), hf', integral_congr_ae hfg']

section smul

variable [NormedField 𝕜] {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G}

/-- The vector-measure integral is homogeneous for scalars of a normed field `𝕜` acting on the
integrand, when the pairing is `𝕜`-linear in its first argument. -/
theorem integral_fun_smul_of_smul_left [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]
    (hB : ∀ (c : 𝕜) x y, B (c • x) y = c • B x y) (c : 𝕜) (f : X → E) :
    ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  simp only [integral_eq_setToFun]
  exact setToFun_smul _ (fun c s x => by simp [transpose_eq_cbmApplyMeasure, hB]) c f

/-- The vector-measure integral is homogeneous for scalars of a normed field `𝕜` acting on the
measure, when the pairing is `𝕜`-linear in its second argument. -/
theorem integral_smul_vectorMeasure_of_smul_right [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G]
    (hB : ∀ (c : 𝕜) x y, B x (c • y) = c • B x y) (c : 𝕜) (f : X → E) :
    ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hf : μ.Integrable f
  · have hμ : c • μ = mapRangeL (lsmul ℝ 𝕜 c) μ := by
      ext s
      simp
    have := map_integral_comp_eq_integral_mapRangeL μ hf (ContinuousLinearMap.id ℝ E)
      (lsmul ℝ 𝕜 c) (lsmul ℝ 𝕜 c) (B := B) (B' := B) (fun x y => by simp [hB])
    simpa [← hμ] using this.symm
  · have hf' : ¬(c • μ).Integrable f := by
      rwa [VectorMeasure.Integrable, variation_smul, ENNReal.smul_def,
        integrable_smul_measure (by simpa using hc) ENNReal.coe_ne_top]
    rw [integral_undef hf, integral_undef hf', smul_zero]

end smul

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
