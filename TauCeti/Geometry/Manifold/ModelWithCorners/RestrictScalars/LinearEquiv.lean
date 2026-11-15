/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# Restriction of scalars and linear changes of model coordinates

Restricting scalars in a boundaryless model commutes with recharting by a continuous
linear equivalence. The model equality identifies both atlases on their existing carrier;
after rewriting it, their comparison is Mathlib's identity diffeomorphism.

For changes of manifold model coordinates, see Kobayashi--Nomizu,
*Foundations of Differential Geometry*, Volume I, Chapter I.
-/

public section

open Set

namespace ModelWithCorners

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {E F H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [TopologicalSpace H]
  (I : ModelWithCorners 𝕜' E H) [I.Boundaryless]

/-- A continuous linear change of coordinates preserves a boundaryless model. -/
instance (e : E ≃L[𝕜'] F) : (I.transContinuousLinearEquiv e).Boundaryless where
  range_eq_univ := by
    rw [I.transContinuousLinearEquiv_range, I.range_eq_univ, image_univ, e.surjective.range_eq]

variable [LinearMap.CompatibleSMul E F 𝕜 𝕜']

variable (𝕜)

/-- Restriction of scalars commutes with a continuous linear change of model coordinates. -/
@[simp]
theorem restrictScalars_transContinuousLinearEquiv (e : E ≃L[𝕜'] F) :
    (I.transContinuousLinearEquiv e).restrictScalars 𝕜 =
      (I.restrictScalars 𝕜).transContinuousLinearEquiv (e.restrictScalars' 𝕜) := by
  ext1 <;> simp

end ModelWithCorners
