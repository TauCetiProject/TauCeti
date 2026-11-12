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

In an affine space over a real seminormed space of dimension greater than one, removing a countable
set from an open ball of positive radius leaves a path-connected set; in particular so does
removing the centre. This is the local form of Mathlib's
`Set.Countable.isPathConnected_compl_of_one_lt_rank`, to which it reduces through the homeomorphism
`OpenPartialHomeomorph.univBall` of the model vector space onto the ball. The punctured ball is
the local input for showing that removing a discrete set from a connected manifold of dimension
greater than one keeps it connected: through a partial homeomorphism to the affine space, every
point of its source has arbitrarily small neighbourhoods whose punctured versions are connected.

## Main declarations

* `Set.Countable.isPathConnected_ball_sdiff`: an open ball with a countable set removed is path
  connected.
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
positive radius with a countable set removed is path connected. -/
theorem _root_.Set.Countable.isPathConnected_ball_sdiff (h : 1 < Module.rank ℝ E) {s : Set P}
    (hs : s.Countable) (x : P) {r : ℝ} (hr : 0 < r) : IsPathConnected (ball x r \ s) := by
  set e := OpenPartialHomeomorph.univBall x r
  have he : Function.Injective e :=
    e.toPartialEquiv.injective_of_source_eq_univ (OpenPartialHomeomorph.univBall_source x r)
  -- `e` maps the whole vector space onto the ball, so `ball x r \ s` is the image of `(e ⁻¹' s)ᶜ`.
  have hrange : range e = ball x r := by
    rw [← image_univ, ← OpenPartialHomeomorph.univBall_source x r, e.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target x hr]
  rw [← hrange, ← image_compl_preimage]
  exact ((hs.preimage he).isPathConnected_compl_of_one_lt_rank h).image
    (OpenPartialHomeomorph.continuous_univBall x r)

/-- In an affine space over a real seminormed space of dimension greater than one, an open ball of
positive radius with its centre removed is path connected. -/
theorem isPathConnected_ball_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : P) {r : ℝ}
    (hr : 0 < r) : IsPathConnected (ball x r \ {x}) :=
  (countable_singleton x).isPathConnected_ball_sdiff h x hr

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
  -- The inverse chart carries the balls about `φ x` inside `φ.target` to a basis of `𝓝 x`.
  have hbasis := (nhds_basis_ball.restrict_subset
    (φ.open_target.mem_nhds (φ.map_source hx))).map φ.symm
  rw [φ.symm_map_nhds_eq hx] at hbasis
  obtain ⟨r, ⟨hr, hbt⟩, hrU⟩ := hbasis.mem_iff.1 hU
  have hsdiff : φ.symm '' ball (φ x) r \ {x} = φ.symm '' (ball (φ x) r \ {φ x}) := by
    rw [(φ.symm.injOn.mono hbt).image_sdiff_subset (singleton_subset_iff.2 (mem_ball_self hr)),
      image_singleton, φ.left_inv hx]
  refine ⟨_, hbasis.mem_of_mem ⟨hr, hbt⟩, hrU, ?_⟩
  rw [hsdiff]
  exact (isConnected_ball_sdiff_singleton h (φ x) hr).image _
    (φ.continuousOn_symm.mono (sdiff_subset.trans hbt))

end TauCeti
