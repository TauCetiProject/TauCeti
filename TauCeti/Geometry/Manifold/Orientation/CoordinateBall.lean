/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Orientation.Inversion

/-!
# Orientation-preserving coordinate balls

Let `M` be a smooth manifold without boundary modelled on a finite-dimensional real inner product
space `E`, with an orientation `oM`, and let `oE` be an orientation of `E`. Every point `x` of `M`
is the centre of a coordinate ball which preserves orientation: an open embedding `e : E → M`
which is a smooth local diffeomorphism, sends `0` to `x`, and preserves orientation from `oE` to
`oM` at every point (`TauCeti.Manifold.Orientation.exists_ball_isOrientationPreservingAt`).

The ball is the inverse of the chart at `x` precomposed with Mathlib's diffeomorphism
`OpenPartialHomeomorph.univBall` of `E` onto a small ball about the image of `x`. Since `E` is
connected, this ball either preserves orientation from `oE` everywhere or reverses it everywhere:
`oE` is the orientation pulled back from `oM` or its opposite
(`TauCeti.Manifold.Orientation.eq_or_eq_neg`). In the second case, precomposing with the reflection
of `E` in a hyperplane, whose determinant is `-1`, turns it into an orientation-preserving ball.
This needs `E` to be nontrivial: in dimension zero a ball is the constant map to `x`, and whether
it preserves orientation from `oE` to `oM` is already decided by `oE` and `oM`.

Coordinate balls of this kind, one preserving and one reversing orientation, are the input of the
oriented connected sum (`TauCeti.ConnectedSum.orientation`).

## Main results

* `TauCeti.Manifold.Orientation.exists_ball_isOrientationPreservingAt`: every point of an oriented
  manifold is the centre of a coordinate ball preserving orientation from a given orientation of
  the model space.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer (2013), Chapter 15 (orientations and their pullbacks).
-/

public section

open Set Function Metric Topology Module
open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- Every point `x` of a smooth manifold without boundary is the centre of a coordinate ball: an
open embedding of the model space which is a smooth local diffeomorphism and sends `0` to `x`. -/
private theorem exists_ball (x : M) :
    ∃ e : E → M, e 0 = x ∧ IsOpenEmbedding e ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e := by
  set φ := chartAt E x
  have hx : φ x ∈ φ.target := φ.map_source (mem_chart_source E x)
  obtain ⟨r, hr, hrφ⟩ := Metric.isOpen_iff.1 φ.open_target _ hx
  set u := OpenPartialHomeomorph.univBall (φ x) r
  have hu : ∀ v, u v ∈ φ.target := fun v ↦ hrφ <| by
    rw [← OpenPartialHomeomorph.univBall_target (φ x) hr]
    exact u.map_source (by simp [u, OpenPartialHomeomorph.univBall_source])
  -- The ball as an open partial homeomorphism defined on all of `E`.
  set Θ := u.trans φ.symm
  have hΘ : Θ.source = univ := by
    simp [Θ, u, OpenPartialHomeomorph.univBall_source, preimage, hu]
  refine ⟨Θ, ?_, Θ.isOpenEmbedding hΘ, fun v ↦ ?_⟩
  · simp [Θ, u, OpenPartialHomeomorph.univBall_apply_zero, φ.left_inv (mem_chart_source E x)]
  · -- `univBall` is a diffeomorphism onto its target, and the inverse chart is a local
    -- diffeomorphism on the target of the chart.
    have hb : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ u v :=
      isLocalDiffeomorphAt_of_eqOn (Φ := PartialDiffeomorph.ofOpenPartialHomeomorph u
        OpenPartialHomeomorph.contDiff_univBall.contDiffOn
        (by rw [OpenPartialHomeomorph.univBall_target _ hr]
            exact OpenPartialHomeomorph.contDiffOn_univBall_symm))
        (by simp [u, OpenPartialHomeomorph.univBall_source]) fun _ _ ↦ by simp
    have hc : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ.symm (u v) :=
      φ.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas x) (hu v)
    exact hb.comp (hg := hc)

/-- **Orientation-preserving coordinate balls.** Let `M` be a smooth manifold without boundary
modelled on a nontrivial finite-dimensional real inner product space `E`, with an orientation `oM`,
and let `oE` be an orientation of `E`. Every point `x` of `M` is the centre of a coordinate ball
`e : E → M`, an open embedding and smooth local diffeomorphism with `e 0 = x`, which preserves
orientation from `oE` to `oM` at every point. -/
theorem exists_ball_isOrientationPreservingAt [Nontrivial E]
    (oE : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (x : M) :
    ∃ e : E → M, e 0 = x ∧ IsOpenEmbedding e ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e ∧
      ∀ v, IsOrientationPreservingAt oE oM e v := by
  obtain ⟨e, he0, he, de⟩ := exists_ball (E := E) x
  have hdf : ∀ v, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e v).IsInvertible := de.isInvertible_mfderiv (by simp)
  have hce : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e := de.contMDiff.of_le (by simp)
  -- On the connected space `E`, `oE` is the pullback of `oM` along `e` or its opposite.
  rcases oE.eq_or_eq_neg (oM.pullback hce hdf oM.card_eq) with h | h
  · exact ⟨e, he0, he, de, (eq_pullback_iff oM hce hdf oM.card_eq).1 h⟩
  · -- `e` reverses orientation from `oE` everywhere; precompose it with a reflection.
    have hrev : ∀ v, IsOrientationReversingAt oE oM e v := fun v ↦ by
      rw [← isOrientationPreservingAt_neg_left, h, neg_neg]
      exact isOrientationPreservingAt_pullback oM hce hdf oM.card_eq v
    obtain ⟨ρ, hρ⟩ := exists_linearIsometryEquiv_isOrientationReversingAt oE
    refine ⟨e ∘ ρ, by simp [he0], he.comp ρ.toHomeomorph.isOpenEmbedding,
      fun v ↦ (ρ.toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph v).comp (hg := de _),
      fun v ↦ (hrev (ρ v)).comp (hρ v)⟩

end TauCeti.Manifold.Orientation
