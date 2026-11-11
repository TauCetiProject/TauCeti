/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# The tangent Lie algebroid

The tangent bundle of a finite-dimensional real manifold, with the identity anchor and the Lie
bracket of vector fields `VectorField.mlieBracket`, is a Lie algebroid,
`TauCeti.LieAlgebroid.tangent`. Its Leibniz rule is the product rule
`VectorField.mlieBracket_smul_right` of the bracket of vector fields, and its Jacobi identity is
`VectorField.leibniz_identity_mlieBracket`. Over a Hausdorff base, every Lie algebroid whose
underlying bundle is a smooth vector bundle maps to it by its anchor
(`TauCeti.LieAlgebroid.anchor_bracket`).
-/

public section

noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff

namespace TauCeti

namespace LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- The tangent Lie algebroid of `M`: the tangent bundle with the identity anchor and the Lie
bracket of smooth vector fields. -/
def tangent : LieAlgebroid I E (TangentSpace I : M → Type _) where
  anchor :=
    { toFun x := ContinuousLinearMap.id ℝ (TangentSpace I x)
      contMDiff_toFun := (contMDiff_hom_bundle_iff _).2 contMDiff_id }
  bracket := LinearMap.mk₂ ℝ
    (fun X Y ↦
      { toFun := mlieBracket I X Y
        contMDiff_toFun := contMDiff_mlieBracket X.contMDiff Y.contMDiff })
    (fun X X' Y ↦ ContMDiffSection.ext fun x ↦
      mlieBracket_add_left (X.contMDiff.mdifferentiableAt (by simp))
        (X'.contMDiff.mdifferentiableAt (by simp)))
    (fun c X Y ↦ ContMDiffSection.ext fun x ↦
      mlieBracket_const_smul_left (X.contMDiff.mdifferentiableAt (by simp)))
    (fun X Y Y' ↦ ContMDiffSection.ext fun x ↦
      mlieBracket_add_right (Y.contMDiff.mdifferentiableAt (by simp))
        (Y'.contMDiff.mdifferentiableAt (by simp)))
    (fun c X Y ↦ ContMDiffSection.ext fun x ↦
      mlieBracket_const_smul_right (Y.contMDiff.mdifferentiableAt (by simp)))
  bracket_self X := ContMDiffSection.ext fun x ↦ by simp
  bracket_bracket X Y Z := ContMDiffSection.ext fun x ↦
    have : IsManifold I (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by simp)
    leibniz_identity_mlieBracket_apply (X.contMDiff.of_le (by simp)).contMDiffAt
      (Y.contMDiff.of_le (by simp)).contMDiffAt (Z.contMDiff.of_le (by simp)).contMDiffAt
  bracket_smul_apply X Y f x := by
    have hfY : ⇑(f • Y) = ⇑f • ⇑Y := funext (ContMDiffSection.smul_apply f Y)
    simp only [LinearMap.mk₂_apply, ContMDiffSection.coeFn_mk, ContinuousLinearMap.id_apply, hfY]
    exact (mlieBracket_smul_right (f.contMDiff.mdifferentiableAt (by simp))
      (Y.contMDiff.mdifferentiableAt (by simp))).trans (add_comm _ _)

@[simp]
theorem tangent_anchor_apply (x : M) (v : TangentSpace I x) : (tangent I M).anchor x v = v :=
  (rfl)

@[simp]
theorem tangent_bracket_apply (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (tangent I M).bracket X Y x = mlieBracket I X Y x :=
  (rfl)

end LieAlgebroid

end TauCeti
