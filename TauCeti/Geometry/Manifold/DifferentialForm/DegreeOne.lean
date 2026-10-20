/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Degree-one forms as sections of the bundle of fibrewise linear maps

A degree-one form with values in a vector bundle `V` assigns to each point an alternating map of
one tangent vector. Mathlib's `ContinuousAlternatingMap.ofSubsingleton` identifies these with
continuous linear maps `TangentSpace I x →L[ℝ] V x`, which are the fibres of the smooth bundle of
fibrewise linear maps. This file shows that the identification preserves regularity, and packages
it as a linear equivalence between smooth `V`-valued one-forms and smooth sections of that bundle.

For the trivial bundle `V = Bundle.Trivial M ℝ` the bundle of fibrewise linear maps is the
cotangent bundle `TauCeti.CotangentBundle I M`, so smooth real one-forms are exactly smooth
sections of the cotangent bundle. This is the comparison used to treat a covector field, such as
the tautological one-form of a cotangent bundle, as a differential form to which the exterior
derivative applies.

## Main declarations

* `TauCeti.isSmoothBundleForm_ofSubsingleton_iff`: a family of linear maps has `C^n` graph in the
  linear-map bundle exactly when the corresponding degree-one form is `C^n`.
* `TauCeti.SmoothBundleForm.degreeOneEquiv`: the linear equivalence between smooth degree-one
  forms and smooth sections of the bundle of fibrewise linear maps.
* `TauCeti.isSmoothForm_ofSubsingleton_iff`, `TauCeti.SmoothForm.degreeOneEquiv`: the same
  statements for fixed-coefficient forms. For `F = ℝ` the bundle of fibrewise linear maps is
  `TauCeti.CotangentBundle I M`, so these identify smooth real one-forms with smooth sections of
  the cotangent bundle.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- A family of fibrewise linear maps is a `C^n` section of the bundle of linear maps
`TangentSpace I x →L[ℝ] V x` exactly when the degree-one form it defines is `C^n`. -/
theorem isSmoothBundleForm_ofSubsingleton_iff {n : WithTop ℕ∞}
    {α : (x : M) → TangentSpace I x →L[ℝ] V x} :
    IsSmoothBundleForm I F V n (fun x ↦
        ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) (0 : Fin 1) (α x)) ↔
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) x (α x)) := by
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
    (ι := Fin 1) 0).toContinuousLinearEquiv
  rw [isSmoothBundleForm_def]
  refine forall_congr' fun x₀ ↦ ?_
  rw [contMDiffAt_continuousAlternatingMap_bundle, contMDiffAt_hom_bundle]
  refine and_congr Iff.rfl ?_
  simp only [ContinuousAlternatingMap.inCoordinates_ofSubsingleton]
  refine ⟨fun h ↦ ?_, fun h ↦ L.contDiff.comp_contMDiffAt h⟩
  exact (L.symm.contDiff.comp_contMDiffAt h).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ by simp [L])

namespace SmoothBundleForm

/-- Smooth `V`-valued degree-one forms are smooth sections of the bundle of fibrewise linear maps
`TangentSpace I x →L[ℝ] V x`, through `ContinuousAlternatingMap.ofSubsingleton` on each fibre. -/
def degreeOneEquiv :
    SmoothBundleForm I F V 1 ≃ₗ[ℝ]
      ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] V x) where
  toFun φ :=
    ⟨fun x ↦ (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) 0).symm (φ.1 x),
      isSmoothBundleForm_ofSubsingleton_iff.mp (by simpa using mem_smoothBundleForms.mp φ.2)⟩
  invFun s :=
    ⟨fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) 0 (s x),
      mem_smoothBundleForms.mpr (isSmoothBundleForm_ofSubsingleton_iff.mpr s.contMDiff)⟩
  map_add' φ ψ := by
    ext x v
    simp
  map_smul' c φ := by
    ext x v
    simp
  left_inv φ := by
    apply Subtype.ext
    ext x v
    simp
  right_inv s := by
    ext x v
    simp

/-- The section of a smooth degree-one form evaluates a tangent vector as the form does. -/
@[simp]
theorem degreeOneEquiv_apply_apply (φ : SmoothBundleForm I F V 1) (x : M)
    (v : TangentSpace I x) :
    degreeOneEquiv φ x v = φ.1 x (fun _ ↦ v) :=
  (rfl)

/-- The degree-one form of a smooth section evaluates a single tangent vector as the section
does. -/
@[simp]
theorem degreeOneEquiv_symm_apply_apply
    (s : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] V x)) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (degreeOneEquiv.symm s).1 x v = s x (v 0) :=
  (rfl)

end SmoothBundleForm

/-- A family of linear functionals `TangentSpace I x →L[ℝ] F` is a `C^n` section of the bundle of
linear maps exactly when the fixed-coefficient degree-one form it defines is `C^n`. For `F = ℝ`
the total space of this bundle is `TauCeti.CotangentBundle I M`. -/
theorem isSmoothForm_ofSubsingleton_iff {n : WithTop ℕ∞}
    {α : (x : M) → TangentSpace I x →L[ℝ] F} :
    IsSmoothForm I n (fun x ↦
        ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) F (0 : Fin 1) (α x)) ↔
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) x (α x)) := by
  rw [isSmoothForm_def, ← isSmoothBundleForm_def]
  exact isSmoothBundleForm_ofSubsingleton_iff

namespace SmoothForm

/-- Smooth `F`-valued one-forms are smooth sections of the bundle of linear maps
`TangentSpace I x →L[ℝ] F`, through `ContinuousAlternatingMap.ofSubsingleton` on each fibre. For
`F = ℝ` these are the smooth sections of `TauCeti.CotangentBundle I M`. This is
`SmoothBundleForm.degreeOneEquiv` for the trivial bundle `Bundle.Trivial M F`. -/
def degreeOneEquiv :
    SmoothForm I M F 1 ≃ₗ[ℝ]
      ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F) :=
  (LinearEquiv.ofEq _ _ <| Submodule.ext fun _ ↦
    mem_smoothForms.trans mem_smoothBundleForms.symm).trans
    (SmoothBundleForm.degreeOneEquiv (V := Bundle.Trivial M F))

/-- The section of a smooth one-form evaluates a tangent vector as the form does. -/
@[simp]
theorem degreeOneEquiv_apply_apply (φ : SmoothForm I M F 1) (x : M) (v : TangentSpace I x) :
    degreeOneEquiv φ x v = φ.1 x (fun _ ↦ v) :=
  (rfl)

/-- The one-form of a smooth section evaluates a single tangent vector as the section does. -/
@[simp]
theorem degreeOneEquiv_symm_apply_apply
    (s : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F)) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (degreeOneEquiv.symm s).1 x v = s x (v 0) :=
  (rfl)

end SmoothForm

end TauCeti
