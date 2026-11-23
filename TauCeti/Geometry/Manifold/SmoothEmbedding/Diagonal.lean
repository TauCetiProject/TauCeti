/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Graph
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The smooth diagonal embedding

The diagonal of a boundaryless smooth manifold is a smooth embedding. Its differential is the
pair of the two identity tangent maps.
-/

public noncomputable section

open Manifold TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The smooth diagonal embedding of a boundaryless manifold. -/
def diagonal : SmoothEmbedding I (I.prod I) ∞ M (M × M) where
  toContMDiffMap := ⟨fun x ↦ (x, x), contMDiff_id.prodMk contMDiff_id⟩
  isSmoothEmbedding_toFun := _root_.ContMDiff.isSmoothEmbedding_graph
    (I := I) (J := I) (n := ∞) (f := _root_.id) contMDiff_id

/-- The diagonal embedding sends `x` to `(x, x)`. -/
@[simp]
theorem diagonal_apply (x : M) : diagonal (I := I) x = (x, x) :=
  (rfl)

/-- The function underlying the diagonal embedding is the diagonal map. -/
theorem coe_diagonal : (diagonal (I := I) : M → M × M) = fun x ↦ (x, x) :=
  funext diagonal_apply

/-- The differential of the diagonal is the pair of the identity tangent maps. -/
theorem hasMFDerivAt_diagonal (x : M) :
    HasMFDerivAt I (I.prod I) (diagonal (I := I) : M → M × M) x
      ((ContinuousLinearMap.id 𝕜 (TangentSpace I x)).prod
        (ContinuousLinearMap.id 𝕜 (TangentSpace I x))) :=
  -- The diagonal function is `(id,id)`; its target tangent model is the product of the two models.
  (hasMFDerivAt_id x).prodMk (hasMFDerivAt_id x)

/-- Under the native product tangent identification, the differential of the diagonal is diagonal.
-/
@[simp]
theorem mfderiv_diagonal (x : M) (v : TangentSpace I x) :
    mfderiv I (I.prod I) (diagonal (I := I) : M → M × M) x v =
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm (v, v) := by
  rw [(hasMFDerivAt_diagonal x).mfderiv, tangentSpaceProdEquiv_symm_apply]
  exact ContinuousLinearMap.prod_apply _ _ _

end TauCeti.SmoothEmbedding
