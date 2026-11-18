/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Topology.MetricSpace.SeparatedBalls

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
* `TauCeti.exists_mem_tendsto_of_forall_eventually_exists_dist_lt`: a map continuous on a punctured
  ball whose values approach a finite set at the centre converges to one of its points. Near the
  centre the values lie in disjoint small balls about the points, and the connected punctured ball
  cannot be split between two of them. This is how a continuous root of a polynomial family over a
  punctured disc acquires a value at a collision of roots.
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

/-- **Limits at a puncture with finitely many candidate values.** In an affine space over a real
seminormed space of dimension greater than one, let `f` be continuous on a punctured ball about
`x`, with values in a metric space, and let `S` be a finite set such that for every `ε > 0` the
values of `f` near `x` lie within `ε` of `S`. Then `f` converges at `x` to a point of `S`. -/
theorem exists_mem_tendsto_of_forall_eventually_exists_dist_lt {Y : Type*} [MetricSpace Y]
    (h : 1 < Module.rank ℝ E) {f : P → Y} {x : P} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousOn f (ball x δ \ {x})) {S : Finset Y}
    (hS : ∀ ε > 0, ∀ᶠ z in 𝓝[≠] x, ∃ s ∈ S, dist (f z) s < ε) :
    ∃ s ∈ S, Filter.Tendsto f (𝓝[≠] x) (𝓝 s) := by
  -- balls of radius `r` about the points of `S` are pairwise far apart
  obtain ⟨r, hr, -, hsep⟩ :=
    exists_pos_closedBall_subset_and_lt_dist (T := S) (U := fun _ ↦ univ) fun _ _ ↦
      Filter.univ_mem
  obtain ⟨ε₁, hε₁, hε₁S⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 (hS r hr))
  set δ' := min δ ε₁
  have hδ' : 0 < δ' := lt_min hδ hε₁
  have hball : ball x δ' \ {x} ⊆ ball x δ \ {x} :=
    sdiff_subset_sdiff_left (ball_subset_ball (min_le_left _ _))
  have hnear : ∀ z ∈ ball x δ' \ {x}, ∃ s ∈ S, dist (f z) s < r := fun z hz ↦
    hε₁S (lt_of_lt_of_le hz.1 (min_le_right _ _)) hz.2
  -- the image of the connected punctured ball lies in the ball about one point `s₁` of `S`
  have hconn := isPathConnected_ball_sdiff_singleton h x hδ'
  obtain ⟨z₁, hz₁⟩ := hconn.nonempty
  obtain ⟨s₁, hs₁, hz₁s⟩ := hnear z₁ hz₁
  have hsub : f '' (ball x δ' \ {x}) ⊆ ball s₁ r := by
    refine hconn.isConnected.isPreconnected.image f (hf.mono hball)
      |>.subset_left_of_subset_union (v := ⋃ s ∈ (S : Set Y) \ {s₁}, ball s r) isOpen_ball
        (isOpen_biUnion fun s _ ↦ isOpen_ball) ?_ ?_
        ⟨f z₁, mem_image_of_mem f hz₁, hz₁s⟩
    · refine Set.disjoint_left.2 fun y hy hy' ↦ ?_
      obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 hy'
      exact hs.2 (eq_of_dist_lt_of_dist_lt (hsep s hs.1 s₁ hs₁) hys hy)
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs, hzs⟩ := hnear z hz
      by_cases hss : s = s₁
      · exact Or.inl (hss ▸ hzs)
      · exact Or.inr (mem_iUnion₂.2 ⟨s, ⟨hs, hss⟩, hzs⟩)
  -- for smaller `ε` the nearby point of `S` is still `s₁`
  refine ⟨s₁, hs₁, Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  filter_upwards [hS (min ε r) (lt_min hε hr), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (ball_mem_nhds x hδ')] with z ⟨s, hs, hzs⟩ hzx hzb
  have hz₁' : dist (f z) s₁ < r := hsub (mem_image_of_mem f ⟨hzb, hzx⟩)
  have hss : s = s₁ :=
    eq_of_dist_lt_of_dist_lt (hsep s hs s₁ hs₁) (lt_of_lt_of_le hzs (min_le_right _ _)) hz₁'
  exact hss ▸ lt_of_lt_of_le hzs (min_le_left _ _)

end TauCeti
