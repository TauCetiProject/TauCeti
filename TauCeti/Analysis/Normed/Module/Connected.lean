/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectedness of punctured balls

In an affine space over a real seminormed space of dimension greater than one, removing the centre
from an open ball of positive radius leaves a path-connected set. This is the local form of
Mathlib's `isPathConnected_compl_singleton_of_one_lt_rank`, to which it reduces through the
homeomorphism `OpenPartialHomeomorph.univBall` of the model vector space onto the ball, sending `0`
to the centre. It is the local input for showing that removing a discrete set from a connected
manifold of dimension greater than one keeps it connected: through a partial homeomorphism to the
affine space, every point of its source has arbitrarily small neighbourhoods whose punctured
versions are connected.

## Main declarations

* `TauCeti.isPathConnected_ball_sdiff_singleton`, `TauCeti.isConnected_ball_sdiff_singleton`: a
  punctured open ball is path connected, hence connected.
* `TauCeti.exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source`: every point in the
  source of a partial homeomorphism to the affine space has arbitrarily small neighbourhoods whose
  punctured versions are connected.
-/

public section

open Metric Set Topology

namespace TauCeti

variable {E P : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace P] [NormedAddTorsor E P]

/-- In an affine space over a real seminormed space of dimension greater than one, an open ball of
positive radius with its centre removed is path connected. -/
theorem isPathConnected_ball_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : P) {r : ℝ}
    (hr : 0 < r) : IsPathConnected (ball x r \ {x}) := by
  set e := OpenPartialHomeomorph.univBall x r
  have he : Function.Injective e :=
    e.toPartialEquiv.injective_of_source_eq_univ (OpenPartialHomeomorph.univBall_source x r)
  have himage : e '' {0}ᶜ = ball x r \ {x} := by
    rw [compl_eq_univ_sdiff, image_sdiff he, ← OpenPartialHomeomorph.univBall_source x r,
      e.image_source_eq_target, OpenPartialHomeomorph.univBall_target x hr, image_singleton,
      OpenPartialHomeomorph.univBall_apply_zero]
  exact himage ▸ (isPathConnected_compl_singleton_of_one_lt_rank h 0).image
    (OpenPartialHomeomorph.continuous_univBall x r)

/-- In an affine space over a real seminormed space of dimension greater than one, an open ball of
positive radius with its centre removed is connected. -/
theorem isConnected_ball_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : P) {r : ℝ}
    (hr : 0 < r) : IsConnected (ball x r \ {x}) :=
  (isPathConnected_ball_sdiff_singleton h x hr).isConnected

variable {X : Type*} [TopologicalSpace X]

/-- If `P` is an affine space over a real seminormed space of dimension greater than one, every
point `x` in the source of a partial homeomorphism `φ : X → P` has arbitrarily small neighbourhoods
`V` with `V \ {x}` connected. -/
theorem exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source
    (h : 1 < Module.rank ℝ E) (φ : OpenPartialHomeomorph X P) {x : X} (hx : x ∈ φ.source)
    {U : Set X} (hU : U ∈ 𝓝 x) : ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}) := by
  -- A ball around `φ x` inside the image of `U` is carried back by the inverse chart.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (φ.image_mem_nhds hx (Filter.inter_mem hU (φ.open_source.mem_nhds hx)))
  have hbt : ball (φ x) r ⊆ φ.target :=
    hball.trans <| by
      rintro _ ⟨y, hy, rfl⟩
      exact φ.map_source hy.2
  have hsdiff : φ.symm '' ball (φ x) r \ {x} = φ.symm '' (ball (φ x) r \ {φ x}) := by
    rw [(φ.symm.injOn.mono hbt).image_sdiff_subset (singleton_subset_iff.2 (mem_ball_self hr)),
      image_singleton, φ.left_inv hx]
  refine ⟨φ.symm '' ball (φ x) r, ?_, ?_, ?_⟩
  · simpa [φ.left_inv hx] using φ.symm.image_mem_nhds (φ.map_source hx) (ball_mem_nhds _ hr)
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hball hz
    rw [φ.left_inv hy.2]
    exact hy.1
  · rw [hsdiff]
    exact (isConnected_ball_sdiff_singleton h (φ x) hr).image _
      (φ.continuousOn_symm.mono (sdiff_subset.trans hbt))

end TauCeti
