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
  [Fintype ι]

/-- The synthesis map of an orthonormal family is a linear isometry from Euclidean coefficient
space into its ambient inner-product space. -/
def synthesisMapIsometry (v : ι → E) (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] E :=
  (TauCeti.synthesisMap 𝕜 v).isometryOfInner fun a b => by
    classical
    rw [TauCeti.synthesisMap_apply, TauCeti.synthesisMap_apply,
      hv.inner_sum _ _ Finset.univ]
    simp [PiLp.inner_apply, mul_comm]

/-- The coordinate isometry sends a coefficient vector to the corresponding linear combination
of the orthonormal family. -/
@[simp]
theorem synthesisMapIsometry_apply (v : ι → E) (hv : Orthonormal 𝕜 v)
    (a : EuclideanSpace 𝕜 ι) :
    synthesisMapIsometry v hv a = ∑ i, a i • v i := by
  simp [synthesisMapIsometry, TauCeti.synthesisMap_apply]

open Classical in
/-- The coordinate isometry sends each standard coordinate vector to the corresponding member of
the orthonormal family. -/
@[simp high]
theorem synthesisMapIsometry_single (v : ι → E) (hv : Orthonormal 𝕜 v) (i : ι) (c : 𝕜) :
    synthesisMapIsometry v hv (EuclideanSpace.single i c) = c • v i := by
  classical
  rw [synthesisMapIsometry_apply]
  simp

end Orthonormal
