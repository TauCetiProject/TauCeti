/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Isometric embeddings into the Hilbert direct sum `WithLp 2 (E × F)`

For complete inner product spaces `E` and `F` over `𝕜` (`[RCLike 𝕜]`), the coordinate projections
`WithLp.fstL 2 𝕜 E F` and `WithLp.sndL 2 𝕜 E F` have adjoints `WithLp.inlL2 𝕜 E F` and
`WithLp.inrL2 𝕜 E F`, acting by `x ↦ (x, 0)` and `y ↦ (0, y)`. These are linear isometries
(`WithLp.isometry_inlL2`, `WithLp.isometry_inrL2`) of operator norm `1` on nontrivial spaces
(`WithLp.norm_inlL2`, `WithLp.norm_inrL2`).
-/

public section

open scoped InnerProductSpace

namespace WithLp

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The isometric embedding `x ↦ (x, 0)` of `E` into the Hilbert direct sum `WithLp 2 (E × F)`,
defined as the adjoint of `WithLp.fstL 2 𝕜 E F`. -/
noncomputable def inlL2 : E →L[𝕜] WithLp 2 (E × F) := (WithLp.fstL 2 𝕜 E F).adjoint

@[simp] theorem inlL2_apply (x : E) : inlL2 𝕜 E F x = WithLp.toLp 2 (x, 0) :=
  ext_inner_left 𝕜 fun _ => by rw [inlL2, ContinuousLinearMap.adjoint_inner_right]; simp

@[simp] theorem adjoint_inlL2 : (inlL2 𝕜 E F).adjoint = WithLp.fstL 2 𝕜 E F :=
  ContinuousLinearMap.adjoint_adjoint _

@[simp] theorem adjoint_fstL : (WithLp.fstL 2 𝕜 E F).adjoint = inlL2 𝕜 E F := (rfl)

/-- The isometric embedding `y ↦ (0, y)` of `F` into the Hilbert direct sum `WithLp 2 (E × F)`,
defined as the adjoint of `WithLp.sndL 2 𝕜 E F`. -/
noncomputable def inrL2 : F →L[𝕜] WithLp 2 (E × F) := (WithLp.sndL 2 𝕜 E F).adjoint

@[simp] theorem inrL2_apply (y : F) : inrL2 𝕜 E F y = WithLp.toLp 2 (0, y) :=
  ext_inner_left 𝕜 fun _ => by rw [inrL2, ContinuousLinearMap.adjoint_inner_right]; simp

@[simp] theorem adjoint_inrL2 : (inrL2 𝕜 E F).adjoint = WithLp.sndL 2 𝕜 E F :=
  ContinuousLinearMap.adjoint_adjoint _

@[simp] theorem adjoint_sndL : (WithLp.sndL 2 𝕜 E F).adjoint = inrL2 𝕜 E F := (rfl)

@[simp] theorem fstL_comp_inlL2 : (WithLp.fstL 2 𝕜 E F).comp (inlL2 𝕜 E F) = 1 := by ext; simp

@[simp] theorem sndL_comp_inrL2 : (WithLp.sndL 2 𝕜 E F).comp (inrL2 𝕜 E F) = 1 := by ext; simp

@[simp] theorem fstL_comp_inrL2 : (WithLp.fstL 2 𝕜 E F).comp (inrL2 𝕜 E F) = 0 := by ext; simp

@[simp] theorem sndL_comp_inlL2 : (WithLp.sndL 2 𝕜 E F).comp (inlL2 𝕜 E F) = 0 := by ext; simp

/-- `WithLp.inlL2 𝕜 E F` is an isometry. -/
theorem isometry_inlL2 : Isometry (inlL2 𝕜 E F) :=
  (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mpr (by simp)

/-- `WithLp.inrL2 𝕜 E F` is an isometry. -/
theorem isometry_inrL2 : Isometry (inrL2 𝕜 E F) :=
  (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mpr (by simp)

/-- On a nontrivial Hilbert space `E`, `WithLp.inlL2 𝕜 E F` has operator norm `1`. -/
@[simp] theorem norm_inlL2 [Nontrivial E] : ‖inlL2 𝕜 E F‖ = 1 := by
  have hsq : ‖inlL2 𝕜 E F‖ ^ 2 = 1 := by
    rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self, adjoint_inlL2, fstL_comp_inlL2, norm_one]
  nlinarith [norm_nonneg (inlL2 𝕜 E F)]

/-- On a nontrivial Hilbert space `F`, `WithLp.inrL2 𝕜 E F` has operator norm `1`. -/
@[simp] theorem norm_inrL2 [Nontrivial F] : ‖inrL2 𝕜 E F‖ = 1 := by
  have hsq : ‖inrL2 𝕜 E F‖ ^ 2 = 1 := by
    rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self, adjoint_inrL2, sndL_comp_inrL2, norm_one]
  nlinarith [norm_nonneg (inrL2 𝕜 E F)]

end WithLp
