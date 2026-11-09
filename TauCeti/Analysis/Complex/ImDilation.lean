/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dilating the normal coordinate of the upper half-plane

`TauCeti.imDilation c` is the real-linear map `x + y i ↦ x + c y i`. It fixes the real axis
pointwise and, for `c < 0`, exchanges the open upper and lower half-planes. This file records its
algebra, its determinant `c`, the resulting change of variables for integrals, integrability and
`Lᵖ` membership on preimages, and the chain rule for undoing it. These are the coordinate changes
behind higher-order reflection across the real axis, `TauCeti.planarReflection`.

It also records the elementary bound `|χ z| ≤ M z.im` on the upper half-plane for a function
vanishing on the real axis with derivative bounded by `M`, which controls boundary layers when
integrating by parts up to the axis.
-/

public section

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal

namespace TauCeti

/-- The real-linear map `x + y i ↦ x + c y i`, which dilates the normal coordinate of the upper
half-plane by `c` and fixes the real axis pointwise. -/
@[expose] def imDilation (c : ℝ) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ⟨z.re, c * z.im⟩
      map_add' := fun z w => Complex.ext (by simp) (by simp [mul_add])
      map_smul' := fun a z => Complex.ext (by simp) (by simp; ring) }

@[simp]
theorem imDilation_apply_re (c : ℝ) (z : ℂ) : (imDilation c z).re = z.re := by
  simp [imDilation]

@[simp]
theorem imDilation_apply_im (c : ℝ) (z : ℂ) : (imDilation c z).im = c * z.im := by
  simp [imDilation]

/-- Dilations of the normal coordinate compose by multiplying the factors. -/
theorem imDilation_imDilation (c c' : ℝ) (z : ℂ) :
    imDilation c (imDilation c' z) = imDilation (c * c') z :=
  Complex.ext rfl (by simp [mul_assoc])

/-- The dilation by one is the identity. -/
@[simp]
theorem imDilation_one_apply (z : ℂ) : imDilation 1 z = z :=
  Complex.ext rfl (by simp)

/-- Points of the real axis are fixed. -/
theorem imDilation_of_im_eq_zero (c : ℝ) {z : ℂ} (hz : z.im = 0) : imDilation c z = z :=
  Complex.ext rfl (by simp [hz])

@[simp]
theorem imDilation_one (c : ℝ) : imDilation c 1 = 1 :=
  imDilation_of_im_eq_zero c (by simp)

@[simp]
theorem imDilation_I (c : ℝ) : imDilation c I = c • I :=
  Complex.ext (by simp) (by simp)

/-- The determinant of the dilation is the dilation factor. -/
theorem det_imDilation (c : ℝ) : LinearMap.det (imDilation c : ℂ →ₗ[ℝ] ℂ) = c := by
  rw [← LinearMap.det_toMatrix basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

/-- A nonzero dilation of the normal coordinate as a continuous linear equivalence. -/
@[expose] def imDilationEquiv {c : ℝ} (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.equivOfInverse (imDilation c) (imDilation c⁻¹)
    (fun z => by rw [imDilation_imDilation, inv_mul_cancel₀ hc, imDilation_one_apply])
    (fun z => by rw [imDilation_imDilation, mul_inv_cancel₀ hc, imDilation_one_apply])

@[simp]
theorem coe_imDilationEquiv {c : ℝ} (hc : c ≠ 0) : ⇑(imDilationEquiv hc) = imDilation c := by
  rfl

/-- A nonzero dilation is a measurable embedding. -/
theorem measurableEmbedding_imDilation {c : ℝ} (hc : c ≠ 0) :
    MeasurableEmbedding (imDilation c) :=
  (imDilationEquiv hc).toHomeomorph.measurableEmbedding

/-- Lebesgue measure scales by the inverse Jacobian under a dilation of the normal coordinate. -/
theorem map_imDilation_volume {c : ℝ} (hc : c ≠ 0) :
    Measure.map (imDilation c) volume = ENNReal.ofReal |c⁻¹| • volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := (imDilation c : ℂ →ₗ[ℝ] ℂ)) (by rwa [det_imDilation])
  rwa [det_imDilation] at h

/-- Dilating the normal coordinate by a factor of modulus at most one does not increase the
norm. -/
theorem norm_imDilation_le {c : ℝ} (hc : |c| ≤ 1) (w : ℂ) : ‖imDilation c w‖ ≤ ‖w‖ := by
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [abs_nonneg c, sq_abs c]
  rw [Complex.norm_def, Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  simp only [Complex.normSq_apply, imDilation_apply_re, imDilation_apply_im]
  nlinarith [mul_self_nonneg w.im]

/-- A function vanishing on the real axis with derivative bounded by `M` is at most `M z.im` on
the upper half-plane. -/
theorem abs_le_mul_im_of_eq_zero_on_real {M : ℝ} {χ : ℂ → ℝ} (hχ : Differentiable ℝ χ)
    (hM : ∀ y, ‖fderiv ℝ χ y‖ ≤ M) (hχ0 : ∀ x : ℝ, χ x = 0) {z : ℂ} (hz : 0 ≤ z.im) :
    |χ z| ≤ M * z.im := by
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ)
    (fun y _ => (hχ y)) (fun y _ => hM y) convex_univ (mem_univ (z.re : ℂ)) (mem_univ z)
  have hz' : z - (z.re : ℂ) = z.im * I := by
    apply Complex.ext <;> simp
  rwa [hχ0, sub_zero, hz', norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hz, Real.norm_eq_abs] at hmv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Change of variables for a dilation of the normal coordinate** on a preimage. -/
theorem setIntegral_comp_imDilation {c : ℝ} (hc : c ≠ 0) (f : ℂ → F) (s : Set ℂ) :
    ∫ z in imDilation c ⁻¹' s, f (imDilation c z) = |c|⁻¹ • ∫ w in s, f w := by
  have he := measurableEmbedding_imDilation hc
  rw [← he.integral_map, ← he.restrict_map, map_imDilation_volume hc, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

omit [NormedSpace ℝ F] in
/-- Integrability transfers along a dilation of the normal coordinate. -/
theorem integrableOn_comp_imDilation_iff {c : ℝ} (hc : c ≠ 0) {f : ℂ → F} {s : Set ℂ} :
    IntegrableOn (fun z => f (imDilation c z)) (imDilation c ⁻¹' s) ↔ IntegrableOn f s := by
  have he := measurableEmbedding_imDilation hc
  rw [IntegrableOn, IntegrableOn, ← Function.comp_def, ← he.integrable_map_iff, ← he.restrict_map,
    map_imDilation_volume hc, Measure.restrict_smul,
    integrable_smul_measure (by simpa using hc) ENNReal.ofReal_ne_top]

omit [NormedSpace ℝ F] in
/-- `Lᵖ` membership transfers along a dilation of the normal coordinate. -/
theorem memLp_comp_imDilation_iff {c : ℝ} (hc : c ≠ 0) {f : ℂ → F} {s : Set ℂ} {p : ℝ≥0∞} :
    MemLp (fun z => f (imDilation c z)) p (volume.restrict (imDilation c ⁻¹' s)) ↔
      MemLp f p (volume.restrict s) := by
  have he := measurableEmbedding_imDilation hc
  rw [← Function.comp_def, ← he.memLp_map_measure_iff, ← he.restrict_map,
    map_imDilation_volume hc, Measure.restrict_smul]
  have h0 : ENNReal.ofReal |c⁻¹| ≠ 0 := by simpa using hc
  refine ⟨fun h => ?_, fun h => h.smul_measure ENNReal.ofReal_ne_top⟩
  have h' := h.smul_measure (ENNReal.inv_ne_top.2 h0)
  rwa [smul_smul, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_smul] at h'

/-- The chain rule for undoing a dilation. -/
theorem fderiv_comp_imDilation_apply {φ : ℂ → ℝ} (hφ : Differentiable ℝ φ) (c : ℝ)
    (w v : ℂ) :
    fderiv ℝ (fun w => φ (imDilation c w)) w v = fderiv ℝ φ (imDilation c w) (imDilation c v) := by
  have h := (hφ (imDilation c w)).hasFDerivAt.comp w (imDilation c).hasFDerivAt
  rw [Function.comp_def] at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply]

end TauCeti
