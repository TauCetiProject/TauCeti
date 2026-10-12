/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Frame

/-!
# Coordinate isometries of orthonormal families

The synthesis map of an orthonormal family is an isometry from Euclidean coefficient space into
the ambient inner-product space. Its coordinate formula and action on the standard basis make the
identified finite-dimensional subspace directly usable in operator constructions.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] {v : ι → E}

/-- The synthesis map of an orthonormal family is a linear isometry from Euclidean coefficient
space into its ambient inner-product space. -/
def synthesisMapIsometry (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] E :=
  (TauCeti.synthesisMap 𝕜 v).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun ι 𝕜).toBasis)
    (EuclideanSpace.basisFun ι 𝕜).orthonormal <| by
    classical
    simpa only [OrthonormalBasis.coe_toBasis, Function.comp_def,
      EuclideanSpace.basisFun_apply, TauCeti.synthesisMap_single, one_smul] using hv

/-- The underlying linear map of the coordinate isometry is the synthesis map. -/
@[simp]
theorem synthesisMapIsometry_toLinearMap (hv : Orthonormal 𝕜 v) :
    hv.synthesisMapIsometry.toLinearMap = TauCeti.synthesisMap 𝕜 v :=
  (rfl)

/-- The coordinate isometry sends a coefficient vector to the corresponding linear combination
of the orthonormal family. -/
@[simp]
theorem synthesisMapIsometry_apply (hv : Orthonormal 𝕜 v)
    (a : EuclideanSpace 𝕜 ι) :
    hv.synthesisMapIsometry a = ∑ i, a i • v i := by
  rw [← LinearIsometry.coe_toLinearMap, synthesisMapIsometry_toLinearMap,
    TauCeti.synthesisMap_apply]

open Classical in
/-- The coordinate isometry sends the single-coordinate vector supported at `i` with coefficient
`c` to `c • v i`. -/
@[simp high]
theorem synthesisMapIsometry_single (hv : Orthonormal 𝕜 v) (i : ι) (c : 𝕜) :
    hv.synthesisMapIsometry (EuclideanSpace.single i c) = c • v i := by
  classical
  rw [synthesisMapIsometry_apply]
  simp

end Orthonormal
