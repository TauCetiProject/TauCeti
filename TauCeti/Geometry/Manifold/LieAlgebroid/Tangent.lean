/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# The tangent Lie algebroid

The tangent bundle of a real manifold modelled on a complete space, with the identity anchor and
the Lie bracket of vector fields `VectorField.mlieBracket`, is a Lie algebroid,
`TauCeti.LieAlgebroid.tangent`. Its Leibniz rule is the product rule
`VectorField.mlieBracket_smul_right` of the bracket of vector fields, and its Jacobi identity is
`VectorField.leibniz_identity_mlieBracket`. Over a Hausdorff base, every Lie algebroid whose
underlying bundle is a smooth vector bundle maps to it by its anchor as a Lie algebra homomorphism
on sections (`TauCeti.LieAlgebroid.anchorLieHom`, via `TauCeti.LieAlgebroid.anchorLieHomOfBracket`
and `TauCeti.LieAlgebroid.anchor_bracket`).
-/

public section

noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff

namespace TauCeti

namespace LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- The tangent Lie algebroid of `M`: the tangent bundle with the identity anchor and the Lie
bracket of smooth vector fields. -/
def tangent : LieAlgebroid I E (TangentSpace I : M → Type _) where
  anchor :=
    { toFun x := ContinuousLinearMap.id ℝ (TangentSpace I x)
      contMDiff_toFun x₀ := by
        -- Read in a tangent trivialization, the identity anchor is locally the constant identity.
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id,
          contMDiffAt_const (c := ContinuousLinearMap.id ℝ E).congr_of_eventuallyEq ?_⟩
        filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E _ x₀)] with x hx
        ext v
        exact Trivialization.continuousLinearMapAt_symmL _ hx v }
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
    simp only [LinearMap.mk₂_apply, ContMDiffSection.coeFn_mk,
      ContMDiffSection.coe_smul_contMDiffMap]
    exact (mlieBracket_smul_right (f.contMDiff.mdifferentiableAt (by simp))
      (Y.contMDiff.mdifferentiableAt (by simp))).trans (add_comm _ _)

@[simp]
theorem tangent_anchor_apply (x : M) (v : TangentSpace I x) : (tangent I M).anchor x v = v :=
  (rfl)

@[simp] theorem tangent_bracket_apply (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (tangent I M).bracket X Y x = mlieBracket I X Y x := (rfl)

/-- The bracket of smooth vector fields, as sections of the tangent Lie algebroid, is the Lie
bracket `VectorField.mlieBracket` of the underlying vector fields. -/
theorem coe_tangent_sectionsEquiv_lie (X Y : (tangent I M).Sections) :
    ⇑((tangent I M).sectionsEquiv ⁅X, Y⁆) =
      mlieBracket I ((tangent I M).sectionsEquiv X) ((tangent I M).sectionsEquiv Y) :=
  funext fun x ↦ by rw [sectionsEquiv_lie, tangent_bracket_apply]

/-- `anchorDeriv` on the tangent Lie algebroid intertwines the section bracket with the commutator
of directional derivatives, without requiring `T2Space M`. -/
theorem tangent_anchorDeriv_bracket
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) :
    (tangent I M).anchorDeriv ((tangent I M).bracket X Y) f =
      (tangent I M).anchorDeriv X ((tangent I M).anchorDeriv Y f) -
        (tangent I M).anchorDeriv Y ((tangent I M).anchorDeriv X f) := by
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
  have hZf (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      ⇑((tangent I M).anchorDeriv Z f) = fun y ↦ mvfderiv I f y (Z y) := funext fun _ ↦ by simp
  ext x; simp only [anchorDeriv_apply, tangent_anchor_apply, tangent_bracket_apply,
    ContMDiffMap.coe_sub, Pi.sub_apply, hZf]
  exact _root_.mvfderiv_mlieBracket f.contMDiff.contMDiffAt (by simp)
    (X.contMDiff.mdifferentiableAt (by simp)) (Y.contMDiff.mdifferentiableAt (by simp))

section AnchorLieHom
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V] (A : LieAlgebroid I F V)

section OfBracket
variable (h : ∀ a b, A.anchorField (A.bracket a b) =
  (tangent I M).bracket (A.anchorField a) (A.anchorField b))

/-- Given that `A.anchorField` intertwines `A.bracket` with the tangent bracket, the anchor applied
to sections is a Lie algebra homomorphism `A.Sections →ₗ⁅ℝ⁆ (tangent I M).Sections`. -/
def anchorLieHomOfBracket : A.Sections →ₗ⁅ℝ⁆ (tangent I M).Sections :=
  { (((tangent I M).sectionsEquiv.symm.restrictScalars ℝ).toLinearMap.comp <|
      (A.anchorField.restrictScalars ℝ).comp (A.sectionsEquiv.restrictScalars ℝ).toLinearMap) with
    map_lie' {_ _} := (tangent I M).sectionsEquiv.injective (by simp [h]) }

@[simp] theorem sectionsEquiv_anchorLieHomOfBracket (s : A.Sections) :
    (tangent I M).sectionsEquiv (A.anchorLieHomOfBracket h s) =
      A.anchorField (A.sectionsEquiv s) := by
  rw [← LieHom.coe_toLinearMap]; simp [anchorLieHomOfBracket]

@[simp] theorem anchorLieHomOfBracket_smul (f : C^∞⟮I, M; ℝ⟯) (s : A.Sections) :
    A.anchorLieHomOfBracket h (f • s) = f • A.anchorLieHomOfBracket h s :=
  (tangent I M).sectionsEquiv.injective (by simp)

@[simp] theorem anchorLieHomOfBracket_lie [FiniteDimensional ℝ E] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I]
    (s : A.Sections) (f : C^∞⟮I, M; ℝ⟯) : ⁅A.anchorLieHomOfBracket h s, f⁆ = ⁅s, f⁆ := by
  rw [Sections.lie_def, Sections.lie_def, sectionsEquiv_anchorLieHomOfBracket]; ext x; simp

end OfBracket

variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]

/-- Over a Hausdorff base, the anchor of any Lie algebroid on a smooth vector bundle induces a Lie
algebra homomorphism `A.Sections →ₗ⁅ℝ⁆ (tangent I M).Sections` intertwining anchor actions. -/
def anchorLieHom : A.Sections →ₗ⁅ℝ⁆ (tangent I M).Sections :=
  A.anchorLieHomOfBracket fun a b ↦ ContMDiffSection.ext fun x ↦ by simp [A.anchor_bracket]

@[simp] theorem sectionsEquiv_anchorLieHom (s : A.Sections) :
    (tangent I M).sectionsEquiv (A.anchorLieHom s) = A.anchorField (A.sectionsEquiv s) :=
  A.sectionsEquiv_anchorLieHomOfBracket _ s

@[simp] theorem anchorLieHom_smul (f : C^∞⟮I, M; ℝ⟯) (s : A.Sections) :
    A.anchorLieHom (f • s) = f • A.anchorLieHom s := A.anchorLieHomOfBracket_smul _ f s

@[simp] theorem anchorLieHom_lie (s : A.Sections) (f : C^∞⟮I, M; ℝ⟯) :
    ⁅A.anchorLieHom s, f⁆ = ⁅s, f⁆ := A.anchorLieHomOfBracket_lie _ s f

end AnchorLieHom
end LieAlgebroid
end TauCeti
