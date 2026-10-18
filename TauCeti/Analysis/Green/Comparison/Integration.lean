/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Area.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OrientationLift
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm

/-!
# Planar area against the canonical manifold orientation

The actual constant orientation lift supplied by the complex model has positive chart signs.
Its chart functional on a scalar multiple of the normalized area form is ordinary planar
integration. Compactly supported integrable scalar coefficients also satisfy the intrinsic
top-form integrability predicate, without an assumed manifold integral identity.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- On the flat complex model, the zero-extended positive coefficient of weighted area is
the scalar times the normalized alternating volume coefficient in any basis. -/
theorem signedInChartAt_fun_smul_manifoldAreaForm (f : ℂ → ℝ)
    (b : Module.Basis (Fin 2) ℝ ℂ) (c z : ℂ) :
    RoughForm.signedInChartAt (I := 𝓘(ℝ, ℂ)) (fun x ↦ f x • manifoldAreaForm x)
      b c (fun _ ↦ 1) z = f z * Complex.orientation.volumeFormL b := by
  have hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) c).source := by simp
  have he : RoughForm.inChartAt (I := 𝓘(ℝ, ℂ)) (fun x ↦ f x • manifoldAreaForm x) c =
      fun x ↦ f x • Complex.orientation.volumeFormL := by
    funext x
    rw [RoughForm.inChartAt_fun_smul, manifoldAreaForm_inChartAt]
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq]
  simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq, Units.val_one,
    Int.cast_one, one_mul, he, ContinuousAlternatingMap.smul_apply, smul_eq_mul] using
    RoughForm.signedInChartAt_apply_of_mem_source
      (I := 𝓘(ℝ, ℂ)) (fun x ↦ f x • manifoldAreaForm x) b c (fun _ ↦ 1) hz

/-- The canonical positive complex orientation lift gives ordinary planar integration of
the actual weighted manifold area form. -/
theorem chartIntegral_model_manifoldAreaForm (f : ℂ → ℝ) (c : ℂ) :
    (Manifold.OrientationLift.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
      (by simp)).chartIntegral (fun x ↦ f x • manifoldAreaForm x) c = ∫ z, f z := by
  rw [Manifold.OrientationLift.chartIntegral_eq_integral
    _ _ Complex.basisOneI c, Manifold.OrientationLift.model_modelOrientation]
  have hs : (fun x : (extChartAt 𝓘(ℝ, ℂ) c).source ↦
      (Manifold.OrientationLift.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
        (by simp)).signAt c x) = fun _ ↦ (1 : ℤˣ) := by
    funext x
    rw [Manifold.OrientationLift.signAt_of_mem _ (by
      simpa only [extChartAt_source] using x.property)]
    exact Manifold.OrientationLift.model_sign _ _ _ _
  rw [hs]
  have ho : _root_.Orientation.signBasis Complex.orientation Complex.basisOneI = 1 :=
    _root_.Orientation.signBasis_orientation Complex.basisOneI
  rw [ho]
  simp_rw [signedInChartAt_fun_smul_manifoldAreaForm, Complex.coe_basisOneI,
    Orientation.volumeFormL_apply, complexAreaForm_one_I, mul_one]
  simp only [Units.val_one, Int.cast_one, one_mul, basisOneI_addHaar]

/-- Genuine compactly supported planar coefficient integrability gives intrinsic top-form
integrability for the actual manifold area form in every basis and every preferred chart. -/
theorem _root_.HasCompactSupport.integrableTopForm_fun_smul_manifoldAreaForm {f : ℂ → ℝ}
    (hc : HasCompactSupport f) (hf : Integrable f) :
    IntegrableTopForm (I := 𝓘(ℝ, ℂ)) (fun x ↦ f x • manifoldAreaForm x) := by
  rw [integrableTopForm_iff]
  refine ⟨hc.isCompact.of_isClosed_subset (_root_.isClosed_tsupport (α := ℂ [⋀^Fin _]→L[ℝ] ℝ) _) ?_,
    ⟨Complex.basisOneI⟩, ?_⟩
  · exact _root_.tsupport_smul_subset_left f
      -- Use the model-space form as an ordinary coefficient function for support arithmetic.
      (show ℂ → ℂ [⋀^Fin 2]→L[ℝ] ℝ from manifoldAreaForm)
  · intro b c
    have heq : RoughForm.signedInChartAt (I := 𝓘(ℝ, ℂ))
        (fun x ↦ f x • manifoldAreaForm x) b c (fun _ ↦ 1) =
        fun z ↦ f z * Complex.orientation.volumeFormL b :=
      funext (signedInChartAt_fun_smul_manifoldAreaForm f b c)
    rw [heq]
    have he := Complex.basisOneI.integrable_apply_basis_iff b
      (fun z ↦ f z • Complex.orientation.volumeFormL)
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      Complex.coe_basisOneI, Orientation.volumeFormL_apply, complexAreaForm_one_I, mul_one,
      basisOneI_addHaar] at he
    simpa only [Orientation.volumeFormL_apply] using he.mpr hf

/-- The canonical oriented manifold integral of integrable compactly supported planar area
is the existing complex Lebesgue integral, including discontinuous scalar coefficients. -/
theorem _root_.HasCompactSupport.integralTopForm_model_manifoldAreaForm {f : ℂ → ℝ}
    (hc : HasCompactSupport f) (hf : Integrable f) :
    integralTopForm (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
      (by simp)) (fun z ↦ f z • manifoldAreaForm z) = ∫ z, f z := by
  rw [Manifold.Orientation.model_eq_mk]
  have hs : _root_.tsupport (α := ℂ [⋀^Fin _]→L[ℝ] ℝ) (fun z ↦ f z • manifoldAreaForm z) ⊆
      (extChartAt 𝓘(ℝ, ℂ) (0 : ℂ)).source := by simp
  exact (integralTopForm_eq_chartIntegral
    (Manifold.OrientationLift.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp))
    (fun z ↦ f z • manifoldAreaForm z) (hc.integrableTopForm_fun_smul_manifoldAreaForm hf)
    0 hs).trans (chartIntegral_model_manifoldAreaForm f 0)

end TauCeti.Green
