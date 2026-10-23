/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
public import TauCeti.Geometry.Manifold.Boundary.SmoothMap
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The sphere as the actual smooth boundary of the closed ball

The standard sphere manifold and the intrinsic boundary manifold of the closed ball are
canonically analytically diffeomorphic. Both directions are the same ambient point; their
smoothness follows from the actual inclusion maps and the boundary smoothness criterion.
-/

public section

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

local instance : IsManifold (𝓡 n) ω
    ((𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :=
  isManifold_boundary (n := n) (closedBall (0 : E) 1) (by simp)

/-- The standard unit sphere is analytically diffeomorphic to the actual intrinsic boundary
of the closed unit ball. The map preserves the underlying ambient point. -/
def sphereDiffeomorphBoundaryClosedBall :
    sphere (0 : E) 1 ≃ₘ^ω⟮𝓡 n, 𝓡 n⟯
      (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) where
  toEquiv :=
    { toFun := fun x ↦ ⟨⟨x.val, sphere_subset_closedBall x.property⟩, by
        rw [boundary_closedBall]
        exact x.property⟩
      invFun := fun x ↦ ⟨x.val.val, by
        simpa only [boundary_closedBall, mem_preimage] using x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  contMDiff_toFun := by
    apply (contMDiff_iff_comp_subtypeVal_boundary (n := n) (by simp)).mpr
    apply (contMDiff_iff_comp_subtypeVal_closedBall (n := n + 1)).mpr
    exact contMDiff_coe_sphere
  contMDiff_invFun := by
    apply ContMDiff.codRestrict_sphere
    exact contMDiff_subtypeVal_closedBall.comp
      (isSmoothEmbedding_subtypeVal_boundary (n := n) (closedBall (0 : E) 1)
        (by simp : (ω : ℕ∞ω) ≠ 0)).contMDiff

/-- The identification of the sphere with the intrinsic boundary preserves its ambient point. -/
@[simp]
theorem sphereDiffeomorphBoundaryClosedBall_apply_coe (x : sphere (0 : E) 1) :
    ((sphereDiffeomorphBoundaryClosedBall (n := n) x).val : E) = x.val := (rfl)

/-- The inverse identification preserves the ambient point of the boundary. -/
@[simp]
theorem sphereDiffeomorphBoundaryClosedBall_symm_apply_coe
    (x : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    ((sphereDiffeomorphBoundaryClosedBall (n := n)).symm x).val = x.val.val := (rfl)

end TauCeti
