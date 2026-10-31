/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Orientation.Preserving

import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Oriented coordinate balls

Every point of a smooth manifold `M` without boundary modelled on a finite-dimensional real inner
product space `E` is the centre of a coordinate ball, an open embedding `E → M` which is a smooth
local diffeomorphism (`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph`). When `E` is
nontrivial, the ball can be chosen to preserve any given orientations of `E` and of `M` at its
centre (`exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt`): at the centre a
ball either preserves or reverses them, and a reversing ball precomposed with a reflection of `E`
preserves them.
-/

public section

open Set Function Topology
open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

/-- **Oriented coordinate balls exist.** If `E` is nontrivial, every point `x` of a smooth manifold
without boundary modelled on `E` is the centre `e 0` of an open embedding `e : E → M`, a smooth
local diffeomorphism, which preserves given orientations of `E` and of `M` at `0`. -/
theorem exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt
    (oE : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (x : M) :
    ∃ e : E → M, e 0 = x ∧ IsOpenEmbedding e ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e ∧
      oE.IsOrientationPreservingAt oM e 0 := by
  obtain ⟨e, he0, he, de⟩ := exists_isOpenEmbedding_isLocalDiffeomorph (F := E) (n := ⊤) x
  obtain hp | hr := oE.isOrientationPreservingAt_or_isOrientationReversingAt oM e 0
    ((de 0).mfderivToContinuousLinearEquiv (by simp))
    ((de 0).mfderivToContinuousLinearEquiv_coe _)
  · exact ⟨e, he0, he, de, hp⟩
  -- A reversing ball is corrected by a reflection of `E`.
  obtain ⟨R, hR⟩ := TauCeti.exists_det_eq_neg_one (F := E)
  exact ⟨e ∘ R, by simpa using he0, he.comp_linearIsometryEquiv R, de.comp_linearIsometryEquiv R,
    isOrientationPreservingAt_comp_of_det_eq_neg_one (by simpa using hr) hR⟩

end TauCeti.Manifold.Orientation
