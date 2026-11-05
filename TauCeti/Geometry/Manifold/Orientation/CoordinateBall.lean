/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Orientation.Pullback

import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Oriented coordinate balls

Every point of a smooth manifold `M` without boundary modelled on a finite-dimensional real inner
product space `E` is the centre of a coordinate ball, an open embedding `E → M` which is a smooth
local diffeomorphism (`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph`). When `E` is
nontrivial, the ball can be chosen to preserve any given orientations of `E` and of `M` at
every point (`exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt`): on the
connected space `E`, its orientation is the pullback orientation or its opposite. In the latter
case, precomposing with a reflection of `E` makes the ball preserve orientations everywhere.
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
local diffeomorphism, which preserves given orientations of `E` and of `M` everywhere. -/
theorem exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt
    (oE : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (x : M) :
    ∃ e : E → M, e 0 = x ∧ IsOpenEmbedding e ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e ∧
      ∀ v, oE.IsOrientationPreservingAt oM e v := by
  obtain ⟨e, he0, he, de⟩ := exists_isOpenEmbedding_isLocalDiffeomorph (F := E) (n := ⊤) x
  have hdf : ∀ v, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e v).IsInvertible := de.isInvertible_mfderiv (by simp)
  have hce : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e := de.contMDiff.of_le (by simp)
  rcases oE.eq_or_eq_neg (oM.pullback hce hdf oM.card_eq) with h | h
  · exact ⟨e, he0, he, de, (eq_pullback_iff oM hce hdf oM.card_eq).1 h⟩
  · have hrev : ∀ v, IsOrientationReversingAt oE oM e v := fun v ↦ by
      rw [← isOrientationPreservingAt_neg_left, h, neg_neg]
      exact isOrientationPreservingAt_pullback oM hce hdf oM.card_eq v
    obtain ⟨R, hR⟩ := TauCeti.exists_det_neg (F := E)
    exact ⟨e ∘ R, by simpa using he0, he.comp_linearIsometryEquiv R,
      de.comp_linearIsometryEquiv R,
      fun v ↦ isOrientationPreservingAt_comp_of_det_neg (hrev (R v)) hR⟩

end TauCeti.Manifold.Orientation
