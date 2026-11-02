/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Smooth coordinate balls

Every point `x` of a `C^n` manifold without boundary modelled on a real inner product space `E` is
the centre of a *coordinate ball*: an open embedding `e : E → M` of the whole model space which is
a `C^n` local diffeomorphism and sends `0` to `x`. Such balls are the input of the connected sum
`TauCeti.ConnectedSum e₁ e₂`, which removes the centres of two of them and glues the punctured
balls.

The ball is the inverse of the chart at `x`, precomposed with Mathlib's diffeomorphism
`OpenPartialHomeomorph.univBall` of `E` onto a small open ball about the image of `x` in the
chart.

## Main results

* `TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph`: every point of a `C^n` manifold without
  boundary modelled on a real inner product space is the centre of a coordinate ball.
-/

public section

open Set Topology

open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞} [IsManifold 𝓘(ℝ, E) n M]

/-- **Smooth coordinate balls.** Every point `x` of a `C^n` manifold without boundary modelled on
a real inner product space `E` is the centre of a coordinate ball: an open embedding `e : E → M`
which is a `C^n` local diffeomorphism and sends `0` to `x`. -/
theorem exists_isOpenEmbedding_isLocalDiffeomorph (x : M) :
    ∃ e : E → M, e 0 = x ∧ IsOpenEmbedding e ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n e := by
  set φ := chartAt E x
  have hx : φ x ∈ φ.target := φ.map_source (mem_chart_source E x)
  obtain ⟨r, hr, hrφ⟩ := Metric.isOpen_iff.1 φ.open_target _ hx
  set u := OpenPartialHomeomorph.univBall (φ x) r
  have hu (v : E) : u v ∈ φ.target := hrφ <| by
    rw [← OpenPartialHomeomorph.univBall_target (φ x) hr]
    exact u.map_source (by simp [u, OpenPartialHomeomorph.univBall_source])
  -- The ball, as an open partial homeomorphism defined on all of `E`.
  set Θ := u.trans φ.symm
  have hΘ : Θ.source = univ := by
    simp [Θ, u, OpenPartialHomeomorph.univBall_source, preimage, hu]
  refine ⟨Θ, ?_, Θ.isOpenEmbedding hΘ, fun v ↦ ?_⟩
  · simp [Θ, u, OpenPartialHomeomorph.univBall_apply_zero, φ.left_inv (mem_chart_source E x)]
  · -- `univBall` is a diffeomorphism onto its target, and the inverse chart is a local
    -- diffeomorphism on the target of the chart.
    have hb : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) n u v :=
      isLocalDiffeomorphAt_of_eqOn (Φ := PartialDiffeomorph.ofOpenPartialHomeomorph u
        OpenPartialHomeomorph.contDiff_univBall.contDiffOn
        (by
          rw [OpenPartialHomeomorph.univBall_target _ hr]
          exact OpenPartialHomeomorph.contDiffOn_univBall_symm))
        (by simp [u, OpenPartialHomeomorph.univBall_source]) fun _ _ ↦ by simp
    have hc : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) n φ.symm (u v) :=
      φ.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas x) (hu v)
    exact hb.comp (hg := hc)

end TauCeti
