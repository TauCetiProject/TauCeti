/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Examples and non-examples of finite-regularity almost complex structures

On a complex normed space `V`, multiplication by `i` is a constant almost complex structure of
every regularity `ℓ`. It is the specialization of the smooth constant structure, and its chart
expression is the constant map `i`.

The identity endomorphism is never an almost complex structure: `id ∘ id = id`, while
`-id ≠ id` on a nontrivial real vector space. In particular a smooth endomorphism field on `ℂ`
equal to `i` on the closed unit disc and to `id` outside the disc of radius `2` squares to `-1`
on the unit disc but is not the field of any structure: the square identity is required at
every point, not on an open set.

## Main declarations

* `ContMDiffAlmostComplexStructure.toEndomorphism_ne_id`: no fibre of a structure is the identity.
* `ContMDiffAlmostComplexStructure.const_complexI_eq_toContMDiff`,
  `ContMDiffAlmostComplexStructure.inChart_const`: the constant structure `i`.
* `ContMDiffAlmostComplexStructure.cutoffSection`,
  `ContMDiffAlmostComplexStructure.not_exists_toEndomorphism_eq_cutoffSection`: the cut-off
  section and its rejection.
-/

public noncomputable section

open Bundle Metric
open scoped ContDiff Manifold

namespace TauCeti

namespace ContMDiffAlmostComplexStructure

section Identity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞}

/-- No fibre of an almost complex structure is the identity, at any regularity: the identity
squares to itself, and `id ≠ -id` on a nontrivial real vector space. -/
theorem toEndomorphism_ne_id (J : ContMDiffAlmostComplexStructure I n M) (x : M) :
    J.toEndomorphism x ≠ ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hJv : J x (J x v) = -v := J.apply_apply x v
  have hxv : J x v = v := congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace I x ↦ A v) h
  rw [hxv, hxv] at hJv
  have h2 : (2 : ℝ) • v = 0 := by
    rw [two_smul]
    nth_rw 1 [hJv]
    exact neg_add_cancel v
  exact hv ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- The identity section is not the endomorphism field of any almost complex structure, at any
regularity, on a nonempty manifold modelled on a nontrivial space. -/
theorem not_exists_toEndomorphism_eq_id [Nonempty M] :
    ¬∃ J : ContMDiffAlmostComplexStructure I n M,
      ∀ x, J.toEndomorphism x = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  rintro ⟨J, hJ⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  exact J.toEndomorphism_ne_id x (hJ x)

end Identity

section ComplexConstant

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Multiplication by `i` on a complex normed space, as a real continuous linear map. -/
def complexI (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] : V →L[ℝ] V :=
  Complex.I • ContinuousLinearMap.id ℝ V

@[simp]
theorem complexI_apply (v : V) : complexI V v = Complex.I • v := (rfl)

/-- Multiplication by `i` squares to minus the identity. -/
theorem complexI_complexI (v : V) : complexI V (complexI V v) = -v := by
  simp [smul_smul]

/-- On a complex normed space, multiplication by `i` is a constant structure of regularity `n`
for every `n`, and it is the regularity-`n` view of the smooth constant structure. -/
theorem const_complexI_eq_toContMDiff (n : ℕ∞) :
    const n (complexI V) complexI_complexI =
      (SmoothAlmostComplexStructure.const (complexI V) complexI_complexI).toContMDiff n := by
  ext x v
  change (const n (complexI V) complexI_complexI).toEndomorphism x v =
    ((SmoothAlmostComplexStructure.const (complexI V) complexI_complexI).toContMDiff n
      ).toEndomorphism x v
  simp

/-- At infinite regularity the constant structure `i` is the smooth constant structure. -/
@[simp]
theorem toSmooth_const_complexI :
    (const ⊤ (complexI V) complexI_complexI).toSmooth =
      SmoothAlmostComplexStructure.const (complexI V) complexI_complexI := by
  ext x v
  change (const ⊤ (complexI V) complexI_complexI).toSmooth.toEndomorphism x v =
    (SmoothAlmostComplexStructure.const (complexI V) complexI_complexI).toEndomorphism x v
  simp

/-- Lowering the regularity of the constant structure `i` gives the constant structure `i`. -/
@[simp]
theorem ofLE_const_complexI {m n : ℕ∞} (h : m ≤ n) :
    (const n (complexI V) complexI_complexI).ofLE h = const m (complexI V) complexI_complexI := by
  ext x v
  change ((const n (complexI V) complexI_complexI).ofLE h).toEndomorphism x v =
    (const m (complexI V) complexI_complexI).toEndomorphism x v
  simp

/-- The chart expression of a constant structure on its model space is the constant map. -/
@[simp]
theorem inChart_const {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ∞)
    (Jc : W →L[ℝ] W) (hJc : ∀ v, Jc (Jc v) = -v) (x z : W) :
    (const n Jc hJc).inChart x z = Jc := by
  rw [inChart_def, const_toEndomorphism_apply]
  exact inCoordinates_tangent_bundle_core_model_space _ _ _ _ _

/-- The chart expression of the constant structure `i` is smooth. -/
theorem contDiff_inChart_const_complexI (n : ℕ∞) (x : V) :
    ContDiff ℝ ∞ ((const n (complexI V) complexI_complexI).inChart x) := by
  rw [show (const n (complexI V) complexI_complexI).inChart x = fun _ ↦ complexI V from
    funext (inChart_const n _ _ x)]
  exact contDiff_const

end ComplexConstant

section Cutoff

/-- A smooth cutoff on `ℂ`, equal to `1` on the closed unit disc and to `0` outside the open
disc of radius `2`. -/
def unitDiscCutoff : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

@[simp]
theorem unitDiscCutoff_rIn : unitDiscCutoff.rIn = 1 := (rfl)

@[simp]
theorem unitDiscCutoff_rOut : unitDiscCutoff.rOut = 2 := (rfl)

theorem unitDiscCutoff_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : unitDiscCutoff z = 1 :=
  unitDiscCutoff.one_of_mem_closedBall (by simpa using hz)

theorem unitDiscCutoff_of_two_le_norm {z : ℂ} (hz : 2 ≤ ‖z‖) : unitDiscCutoff z = 0 :=
  unitDiscCutoff.zero_of_le_dist (by simpa using hz)

/-- The endomorphism field `χ • i + (1 - χ) • id` on `ℂ`, where `χ` is `unitDiscCutoff`. -/
def cutoffField (z : ℂ) : ℂ →L[ℝ] ℂ :=
  unitDiscCutoff z • complexI ℂ + (1 - unitDiscCutoff z) • ContinuousLinearMap.id ℝ ℂ

/-- The cut-off field is smooth. -/
theorem contDiff_cutoffField : ContDiff ℝ ∞ cutoffField := by
  have hχ : ContDiff ℝ ∞ (unitDiscCutoff : ℂ → ℝ) := unitDiscCutoff.contDiff
  exact (hχ.smul contDiff_const).add ((contDiff_const.sub hχ).smul contDiff_const)

theorem cutoffField_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : cutoffField z = complexI ℂ := by
  ext v
  simp [cutoffField, unitDiscCutoff_of_norm_le_one hz]

theorem cutoffField_of_two_le_norm {z : ℂ} (hz : 2 ≤ ‖z‖) :
    cutoffField z = ContinuousLinearMap.id ℝ ℂ := by
  simp [cutoffField, unitDiscCutoff_of_two_le_norm hz]

/-- On the closed unit disc the cut-off field squares to minus the identity. -/
theorem cutoffField_cutoffField_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (v : ℂ) :
    cutoffField z (cutoffField z v) = -v := by
  rw [cutoffField_of_norm_le_one hz]
  exact complexI_complexI v

/-- Outside the disc of radius `2` the cut-off field fails the square identity. -/
theorem cutoffField_comp_ne_neg_id {z : ℂ} (hz : 2 ≤ ‖z‖) :
    (cutoffField z).comp (cutoffField z) ≠ -ContinuousLinearMap.id ℝ ℂ := by
  rw [cutoffField_of_two_le_norm hz]
  intro h
  have h1 := congrArg (fun A : ℂ →L[ℝ] ℂ ↦ A 1) h
  norm_num at h1

/-- The cut-off field as a smooth section of the tangent endomorphism bundle of `ℂ`. -/
def cutoffSection :
    ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ) ∞
      (fun z : ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) z) :=
  ⟨cutoffField, by
    intro x
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [inCoordinates_tangent_bundle_core_model_space] using
      contDiff_cutoffField.contMDiff x⟩

@[simp]
theorem cutoffSection_apply (z : ℂ) : cutoffSection z = cutoffField z := (rfl)

/-- The smooth cut-off section is not the field of an almost complex structure of any regularity:
it squares to `-1` on the unit disc, but the identity is required at every point. -/
theorem not_exists_toEndomorphism_eq_cutoffSection {n : ℕ∞} :
    ¬∃ J : ContMDiffAlmostComplexStructure 𝓘(ℝ, ℂ) n ℂ,
      ∀ z, J.toEndomorphism z = cutoffSection z := by
  rintro ⟨J, hJ⟩
  have h2 : 2 ≤ ‖(2 : ℂ)‖ := by simp
  refine J.toEndomorphism_ne_id 2 ?_
  rw [hJ, cutoffSection_apply, cutoffField_of_two_le_norm h2]
  rfl

end Cutoff

end ContMDiffAlmostComplexStructure

end TauCeti
