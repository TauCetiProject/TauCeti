/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Pulling back continuous bilinear maps

A continuous linear map `u : W →L[𝕜] V` pulls a continuous bilinear map `B` on `V` back to the
bilinear map `B (u ·) (u ·)` on `W`. This operation is itself continuous and linear in `B`
(`ContinuousLinearMap.pullbackBilinL`), so that it commutes with derivatives of families of
bilinear maps, such as the coordinate expressions of metrics.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V W G : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pulling a continuous bilinear map back along a continuous linear map `u`,
`B ↦ B (u ·) (u ·)`, as a continuous linear map in `B`. -/
@[expose] def pullbackBilinL (u : W →L[𝕜] V) : (V →L[𝕜] V →L[𝕜] G) →L[𝕜] W →L[𝕜] W →L[𝕜] G :=
  (compL 𝕜 W (V →L[𝕜] G) (W →L[𝕜] G) ((compL 𝕜 W V G).flip u)).comp
    ((compL 𝕜 W V (V →L[𝕜] G)).flip u)

@[simp]
theorem pullbackBilinL_apply (u : W →L[𝕜] V) (B : V →L[𝕜] V →L[𝕜] G) (v w : W) :
    pullbackBilinL u B v w = B (u v) (u w) :=
  rfl

end ContinuousLinearMap
