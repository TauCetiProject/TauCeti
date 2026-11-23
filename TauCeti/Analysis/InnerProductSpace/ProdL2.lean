/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Isometric embeddings into the `L²` direct sum `WithLp 2 (E × F)`

For inner product spaces `E` and `F` over `𝕜` (`[RCLike 𝕜]`), `WithLp.inlL2 𝕜 E F` and
`WithLp.inrL2 𝕜 E F` are the coordinate embeddings `x ↦ (x, 0)` and `y ↦ (0, y)` into
`WithLp 2 (E × F)`. These are linear isometries (`WithLp.isometry_inlL2`, `WithLp.isometry_inrL2`)
of operator norm `1` on nontrivial spaces (`WithLp.norm_inlL2`, `WithLp.norm_inrL2`). When `E` and
`F` are complete, they are the Hilbert-space adjoints of the coordinate projections
`WithLp.fstL 2 𝕜 E F` and `WithLp.sndL 2 𝕜 E F` (`WithLp.adjoint_fstL`, `WithLp.adjoint_sndL`,
`WithLp.adjoint_inlL2`, `WithLp.adjoint_inrL2`).
-/

public section

namespace WithLp

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The isometric embedding `x ↦ (x, 0)` of `E` into the `L²` direct sum `WithLp 2 (E × F)`. -/
def inlL2 : E →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl 𝕜 E F)

@[simp] theorem inlL2_apply (x : E) : inlL2 𝕜 E F x = WithLp.toLp 2 (x, 0) := by rfl

/-- The isometric embedding `y ↦ (0, y)` of `F` into the `L²` direct sum `WithLp 2 (E × F)`. -/
def inrL2 : F →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr 𝕜 E F)

@[simp] theorem inrL2_apply (y : F) : inrL2 𝕜 E F y = WithLp.toLp 2 (0, y) := by rfl

@[simp] theorem fstL_comp_inlL2 : (WithLp.fstL 2 𝕜 E F).comp (inlL2 𝕜 E F) = 1 := by ext; simp

@[simp] theorem sndL_comp_inrL2 : (WithLp.sndL 2 𝕜 E F).comp (inrL2 𝕜 E F) = 1 := by ext; simp

@[simp] theorem fstL_comp_inrL2 : (WithLp.fstL 2 𝕜 E F).comp (inrL2 𝕜 E F) = 0 := by ext; simp

@[simp] theorem sndL_comp_inlL2 : (WithLp.sndL 2 𝕜 E F).comp (inlL2 𝕜 E F) = 0 := by ext; simp

/-- `WithLp.inlL2 𝕜 E F` is an isometry. -/
theorem isometry_inlL2 : Isometry (inlL2 𝕜 E F) :=
  AddMonoidHomClass.isometry_of_norm _ fun _ => by simp

/-- `WithLp.inrL2 𝕜 E F` is an isometry. -/
theorem isometry_inrL2 : Isometry (inrL2 𝕜 E F) :=
  AddMonoidHomClass.isometry_of_norm _ fun _ => by simp

/-- On a nontrivial inner product space `E`, `WithLp.inlL2 𝕜 E F` has operator norm `1`. -/
@[simp] theorem norm_inlL2 [Nontrivial E] : ‖inlL2 𝕜 E F‖ = 1 :=
  (inlL2 𝕜 E F).homothety_norm fun _ => by simp

/-- On a nontrivial inner product space `F`, `WithLp.inrL2 𝕜 E F` has operator norm `1`. -/
@[simp] theorem norm_inrL2 [Nontrivial F] : ‖inrL2 𝕜 E F‖ = 1 :=
  (inrL2 𝕜 E F).homothety_norm fun _ => by simp

section Adjoint

variable [CompleteSpace E] [CompleteSpace F]

@[simp] theorem adjoint_fstL : (WithLp.fstL 2 𝕜 E F).adjoint = inlL2 𝕜 E F :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun _ _ => by simp).symm

@[simp] theorem adjoint_inlL2 : (inlL2 𝕜 E F).adjoint = WithLp.fstL 2 𝕜 E F := by
  rw [← adjoint_fstL, ContinuousLinearMap.adjoint_adjoint]

@[simp] theorem adjoint_sndL : (WithLp.sndL 2 𝕜 E F).adjoint = inrL2 𝕜 E F :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun _ _ => by simp).symm

@[simp] theorem adjoint_inrL2 : (inrL2 𝕜 E F).adjoint = WithLp.sndL 2 𝕜 E F := by
  rw [← adjoint_sndL, ContinuousLinearMap.adjoint_adjoint]

end Adjoint

end WithLp
