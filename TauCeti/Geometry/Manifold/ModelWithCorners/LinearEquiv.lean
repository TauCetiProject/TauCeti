/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Linear changes of model coordinates

Composing a model with a continuous linear equivalence changes its vector-space coordinates,
not the smooth structure groupoid on its chart space. Thus the same maximal atlas can be used
before and after changing model coordinates, even for models with boundary or corners.

`ModelWithCorners.contDiffGroupoid_transContinuousLinearEquiv` gives this equality at every
regularity. The identity and composition laws for `ModelWithCorners.transContinuousLinearEquiv`
make repeated coordinate changes simplify to a single change; in particular a change followed
by its inverse returns the original model.

The groupoid comparison uses the same conjugation argument as Mathlib's
`ContinuousLinearEquiv.instIsManifoldtransContinuousLinearEquiv`, before choosing an atlas.
Mathlib's `ContinuousLinearEquiv.toTransContinuousLinearEquiv` already supplies the identity
comparison diffeomorphism on any charted manifold.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Volume I, Chapter I.
-/

public section

open Set
open scoped ContDiff

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H)

/-- The identity linear change of coordinates leaves the model unchanged. -/
@[simp]
theorem transContinuousLinearEquiv_refl :
    I.transContinuousLinearEquiv (ContinuousLinearEquiv.refl 𝕜 E) = I := by
  ext1 <;> simp [ModelWithCorners.target_eq]

/-- Successive linear changes of coordinates agree with their composite. -/
@[simp]
theorem transContinuousLinearEquiv_trans (e : E ≃L[𝕜] F) (f : F ≃L[𝕜] G) :
    (I.transContinuousLinearEquiv e).transContinuousLinearEquiv f =
      I.transContinuousLinearEquiv (e.trans f) := by
  ext1 <;> simp [ModelWithCorners.target_eq, Function.comp_def]

private theorem contDiffGroupoid_le_transContinuousLinearEquiv (e : E ≃L[𝕜] F)
    (n : ℕ∞ω) : contDiffGroupoid n I ≤ contDiffGroupoid n (I.transContinuousLinearEquiv e) := by
  rw [contDiffGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact e.contDiff.comp_contDiffOn
    (hfs.comp e.symm.contDiff.contDiffOn (by
      simp [preimage_comp, range_comp, mapsTo_iff_subset_preimage,
        ContinuousLinearEquiv.image_eq_preimage_symm]))

/-- A continuous linear change of model coordinates leaves the smooth structure groupoid on
`H` unchanged. No boundarylessness or finite-dimensionality assumption is needed. -/
@[simp]
theorem contDiffGroupoid_transContinuousLinearEquiv (e : E ≃L[𝕜] F) (n : ℕ∞ω) :
    contDiffGroupoid n (I.transContinuousLinearEquiv e) = contDiffGroupoid n I := by
  apply le_antisymm
  · simpa using
      contDiffGroupoid_le_transContinuousLinearEquiv (I.transContinuousLinearEquiv e) e.symm n
  · exact contDiffGroupoid_le_transContinuousLinearEquiv I e n

/-- The maximal atlas of a charted space is unchanged by a continuous linear change of model
coordinates. This compares the actual sets of charts, not just manifold instances. -/
@[simp]
theorem maximalAtlas_transContinuousLinearEquiv {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (e : E ≃L[𝕜] F) (n : ℕ∞ω) :
    IsManifold.maximalAtlas (I.transContinuousLinearEquiv e) n M =
      IsManifold.maximalAtlas I n M := by
  simp only [IsManifold.maximalAtlas, contDiffGroupoid_transContinuousLinearEquiv]

end ModelWithCorners
