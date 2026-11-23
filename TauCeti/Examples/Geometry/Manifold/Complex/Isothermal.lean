/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Isothermal
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import TauCeti.Analysis.Complex.Beltrami.Isothermal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum

/-!
# Examples: smooth isothermal comparisons

These examples treat both planar orientations at a nonzero centre, a nonconstant smooth
almost complex structure, the projective line, disconnected planes, and empty surfaces.
The comparisons use the tangent endomorphisms and isothermal identity maps.

## Used results

* `TauCeti.Beltrami.exists_centered_smooth_isothermal_chart`
* `TauCeti.IsothermalSurface.contMDiff_homeomorph`
* `TauCeti.IsothermalSurface.contMDiff_homeomorph_symm`
-/

public section

open Complex Set TauCeti TauCeti.SmoothAlmostComplexStructure
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti.Examples.Isothermal

/-- Standard planar coordinates are obtained at a nonzero centre. -/
theorem standard_nonzero_center :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, 2 + I ∈ e.source ∧ e (2 + I) = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (I * v) = I * fderiv ℝ e z v := by
  obtain ⟨e, hc, hec, -, he, hes, hlin⟩ :=
    Beltrami.exists_centered_smooth_isothermal_chart
      (J := fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ) contDiff_const.contDiffOn
      isOpen_univ (mem_univ (2 + I)) (fun z _ v ↦ by simp [← mul_assoc])
  exact ⟨e, hc, hec, he, hes, fun z hz v ↦ by simpa using hlin z hz v⟩

/-- The opposite complex orientation has centred smooth charts with the reversed intertwining. -/
theorem reversed_nonzero_center :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, 2 + I ∈ e.source ∧ e (2 + I) = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (-I * v) = I * fderiv ℝ e z v := by
  obtain ⟨e, hc, hec, -, he, hes, hlin⟩ :=
    Beltrami.exists_centered_smooth_isothermal_chart
      (J := fun _ ↦ -I • ContinuousLinearMap.id ℝ ℂ) contDiff_const.contDiffOn
      isOpen_univ (mem_univ (2 + I)) (fun z _ v ↦ by simp [← mul_assoc])
  exact ⟨e, hc, hec, he, hes, fun z hz v ↦ by simpa using hlin z hz v⟩

/-- A smooth planar field obtained by stretching the real coordinate exponentially. -/
def stretchField (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (-Real.exp z.re) • (Complex.imCLM.smulRight (1 : ℂ)) +
    Real.exp (-z.re) • (Complex.reCLM.smulRight I)

@[simp]
theorem stretchField_re (z v : ℂ) : (stretchField z v).re = -Real.exp z.re * v.im := by
  simp [stretchField, ContinuousLinearMap.smulRight_apply, -Complex.ofReal_neg,
    Complex.exp_ofReal_re, Complex.exp_ofReal_im]

@[simp]
theorem stretchField_im (z v : ℂ) : (stretchField z v).im = Real.exp (-z.re) * v.re := by
  simp [stretchField, ContinuousLinearMap.smulRight_apply, -Complex.ofReal_neg,
    Complex.exp_ofReal_re, Complex.exp_ofReal_im]

/-- The stretched field is smooth in the actual real endomorphism space. -/
theorem stretchField_contDiff : ContDiff ℝ ∞ stretchField := by
  exact ((Complex.reCLM.contDiff.exp).neg.smul contDiff_const).add
    ((Complex.reCLM.contDiff.neg.exp).smul contDiff_const)

/-- Each stretched endomorphism squares to minus the identity. -/
theorem stretchField_sq (z v : ℂ) : stretchField z (stretchField z v) = -v := by
  apply Complex.ext <;> simp [Real.exp_neg, Real.exp_ne_zero]

/-- The stretched field is genuinely nonconstant. -/
theorem stretchField_ne : stretchField 0 ≠ stretchField 1 := by
  intro h
  have hh := congrArg (fun A : ℂ →L[ℝ] ℂ ↦ (A I).re) h
  have he : Real.exp 1 ≠ 1 := ne_of_gt (Real.one_lt_exp_iff.mpr (by norm_num))
  exact he (by simpa using hh.symm)

/-- The nonconstant field supplies an actual smooth tangent endomorphism section. -/
def stretchStructure : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ where
  toEndomorphism := ⟨stretchField, by
    intro x
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa [inCoordinates_tangent_bundle_core_model_space] using
      (stretchField_contDiff.contDiffAt (x := x)).contMDiffAt⟩
  square_neg := by
    intro x
    ext v
    exact stretchField_sq x v

/-- The almost complex structure has different endomorphisms at two points. -/
theorem stretchStructure_ne : stretchStructure.toEndomorphism 0 ≠
    stretchStructure.toEndomorphism 1 := stretchField_ne

/-- The identity to the surface is smooth for the nonconstant structure. -/
theorem stretch_identity :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (IsothermalSurface.homeomorph stretchStructure) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (IsothermalSurface.homeomorph stretchStructure).symm :=
  ⟨IsothermalSurface.contMDiff_homeomorph stretchStructure,
    IsothermalSurface.contMDiff_homeomorph_symm stretchStructure⟩

/-- The nonconstant structure is represented by the pointwise identity diffeomorphism. -/
theorem stretch_identity_value (x : ℂ) :
    IsothermalSurface.diffeomorph stretchStructure
      ((IsothermalSurface.homeomorph stretchStructure).symm x) = x := by
  rw [IsothermalSurface.coe_diffeomorph]
  exact (IsothermalSurface.homeomorph stretchStructure).apply_symm_apply x

/-- The smooth identity intertwines the complex structure and the given field. -/
theorem stretch_intertwining :
    IsPseudoholomorphic (ofComplexManifold ℂ (IsothermalSurface stretchStructure))
      stretchStructure (IsothermalSurface.diffeomorph stretchStructure) := by
  simpa only [IsothermalSurface.coe_diffeomorph] using
    IsothermalSurface.isPseudoholomorphic_homeomorph stretchStructure

/-- The original C¹ comparison follows from the smooth maps on the same surfaces. -/
theorem original_c1_identity :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (IsothermalSurface.homeomorph stretchStructure) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (IsothermalSurface.homeomorph stretchStructure).symm :=
  ⟨(IsothermalSurface.contMDiff_homeomorph stretchStructure).of_le (by simp),
    (IsothermalSurface.contMDiff_homeomorph_symm stretchStructure).of_le (by simp)⟩

/-- The sphere uses the same smooth identity comparison in both directions. -/
theorem sphere_identity :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (IsothermalSurface.homeomorph (ofComplexManifold ℂ (OnePoint ℂ))) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (IsothermalSurface.homeomorph (ofComplexManifold ℂ (OnePoint ℂ))).symm :=
  ⟨IsothermalSurface.contMDiff_homeomorph _, IsothermalSurface.contMDiff_homeomorph_symm _⟩

/-- The disconnected plane sum has both smooth identity directions. -/
theorem disconnected_identity :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (IsothermalSurface.homeomorph (ofComplexManifold ℂ (ℂ ⊕ ℂ))) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (IsothermalSurface.homeomorph (ofComplexManifold ℂ (ℂ ⊕ ℂ))).symm :=
  ⟨IsothermalSurface.contMDiff_homeomorph _,
    IsothermalSurface.contMDiff_homeomorph_symm _⟩

section Empty

universe u

/-- The empty base carries its native empty complex atlas in every universe. -/
local instance instChartedSpaceEmpty : ChartedSpace ℂ PEmpty.{u + 1} := ChartedSpace.empty ℂ PEmpty

/-- Literal empty surfaces in arbitrary universes instantiate the whole native smooth theorem. -/
theorem empty_identity :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (IsothermalSurface.homeomorph (ofComplexManifold ℂ PEmpty.{u + 1})) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (IsothermalSurface.homeomorph (ofComplexManifold ℂ PEmpty.{u + 1})).symm :=
  ⟨IsothermalSurface.contMDiff_homeomorph _,
    IsothermalSurface.contMDiff_homeomorph_symm _⟩

end Empty

end TauCeti.Examples.Isothermal
