/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Cutting a set by a sphere

Removing the sphere `sphere x ρ` from a set `s` leaves two pieces: the *near side*
`s ∩ ball x ρ`, of the points of `s` closer to `x` than `ρ`, and the *far side*
`s \ closedBall x ρ`, of those further away. This file records that they cover `s \ sphere x ρ`,
that they are disjoint, that the two sides together with the cut cover all of `s` (also after
applying an arbitrary map), and — when `s` is open, so that both sides are open — that a
preconnected subset of `s` missing the sphere lies entirely in one of them.

Nothing beyond the containments `ball x ρ ⊆ closedBall x ρ` and `sphere x ρ ⊆ closedBall x ρ`, and
the openness of a ball against the closedness of a closed ball, is used, so `s` is an arbitrary set
in an arbitrary pseudo-metric space.

The one quantitative statement is about *shrinking* the cut. Once the far side at radius `0`,
`s \ closedBall x 0`, has two points with distinct images, the far side keeps both of them for
every small enough `ρ`, so its image stays at least as wide as the distance between those two
images: the far side does not degenerate as the cut shrinks. Distinctness of the two images is what
forces a genuine metric, rather than pseudo-metric, structure on the target, and that statement
alone asks for one. In a metric space `s \ closedBall x 0 = s \ {x}`, which is `s` itself when the
cut point lies off `s`.

The motivating application is Carathéodory's boundary correspondence, in
`TauCeti/Analysis/Complex/Conformal/Crosscut/Basic.lean` and
`TauCeti/Analysis/Complex/Conformal/CutDiameter.lean`: there `X = ℂ` and the sphere is the
*circular crosscut* of a plane domain at a boundary point, whose near side is the approach region
along which the boundary behaviour of a conformal map is read off. Nothing here is specific to that
use, and Mathlib has no form of the decomposition.

## Main results

* `TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` — the two sides cover the cut set.
* `TauCeti.disjoint_inter_ball_sdiff_closedBall` — the two sides are disjoint, and
  `TauCeti.disjoint_inter_ball_inter_sphere`, `TauCeti.disjoint_sdiff_closedBall_inter_sphere` —
  each of them is disjoint from the cut.
* `TauCeti.eq_inter_ball_union_sdiff_closedBall_union_inter_sphere` — the two sides and the cut
  cover the whole set, and
  `TauCeti.image_eq_image_inter_ball_union_image_sdiff_closedBall_union_image_inter_sphere` is its
  image under an arbitrary map.
* `TauCeti.subset_inter_ball_or_subset_sdiff_closedBall` — a preconnected subset of an open cut set
  missing the sphere lies on one side of it.
* `TauCeti.exists_pos_forall_le_diam_image_sdiff_closedBall` — once the far side at radius `0` has
  a nontrivial image, the image of the far side stays at least as wide as a fixed positive number
  for every small enough radius.
-/

public section

namespace TauCeti

open Metric Set

variable {X : Type*} [PseudoMetricSpace X] {x : X} {ρ : ℝ}

/-- **A circular cut splits a set into a near side and a far side.** Removing the sphere
`sphere x ρ` from a set `s` leaves the points of `s` at distance less than `ρ` from `x` together
with those at distance more than `ρ`. -/
theorem sdiff_sphere_eq_inter_ball_union_sdiff_closedBall {s : Set X} :
    s \ sphere x ρ = s ∩ ball x ρ ∪ s \ closedBall x ρ := by
  ext
  simp [← and_or_left, lt_or_lt_iff_ne]

/-- The two sides of a circular cut are disjoint, the near side lying inside `closedBall x ρ` and
the far side outside it. -/
theorem disjoint_inter_ball_sdiff_closedBall {s : Set X} :
    Disjoint (s ∩ ball x ρ) (s \ closedBall x ρ) :=
  disjoint_sdiff_right.mono_left (inter_subset_right.trans ball_subset_closedBall)

/-- The near side of a circular cut misses the cut itself, the ball and the sphere being
disjoint. -/
theorem disjoint_inter_ball_inter_sphere {s : Set X} :
    Disjoint (s ∩ ball x ρ) (s ∩ sphere x ρ) :=
  sphere_disjoint_ball.symm.mono inter_subset_right inter_subset_right

/-- The far side of a circular cut misses the cut itself, the sphere lying in the closed ball. -/
theorem disjoint_sdiff_closedBall_inter_sphere {s : Set X} :
    Disjoint (s \ closedBall x ρ) (s ∩ sphere x ρ) :=
  disjoint_sdiff_left.mono_right (inter_subset_right.trans sphere_subset_closedBall)

/-- **A circular cut splits a set into a near side, a far side and the cut.** The three-piece form
of `TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall`. -/
theorem eq_inter_ball_union_sdiff_closedBall_union_inter_sphere {s : Set X} :
    s = s ∩ ball x ρ ∪ s \ closedBall x ρ ∪ s ∩ sphere x ρ := by
  rw [← sdiff_sphere_eq_inter_ball_union_sdiff_closedBall, sdiff_union_inter]

/-- **The image of a circular cut is the union of the images of its two sides and the cut.** This
is the image form of `TauCeti.eq_inter_ball_union_sdiff_closedBall_union_inter_sphere`; the target
of `f` carries no structure. -/
theorem image_eq_image_inter_ball_union_image_sdiff_closedBall_union_image_inter_sphere
    {Y : Type*} (f : X → Y) {s : Set X} :
    f '' s = f '' (s ∩ ball x ρ) ∪ f '' (s \ closedBall x ρ) ∪ f '' (s ∩ sphere x ρ) := by
  rw [← image_union, ← image_union, ← eq_inter_ball_union_sdiff_closedBall_union_inter_sphere]

/-- **A connected subset of an open set missing a circular cut lies on one side of it.** This is
the separation statement the decomposition exists for: the two sides are open and disjoint, so a
preconnected subset of their union cannot meet both. Only openness of the cut set is used. -/
theorem subset_inter_ball_or_subset_sdiff_closedBall {s S : Set X} (hs : IsOpen s)
    (hS : IsPreconnected S) (hSsub : S ⊆ s \ sphere x ρ) :
    S ⊆ s ∩ ball x ρ ∨ S ⊆ s \ closedBall x ρ :=
  hS.subset_or_subset (hs.inter isOpen_ball) (hs.sdiff isClosed_closedBall)
    disjoint_inter_ball_sdiff_closedBall
    (hSsub.trans_eq sdiff_sphere_eq_inter_ball_union_sdiff_closedBall)

/-! ## The far side does not degenerate -/

variable {Y : Type*} [MetricSpace Y] {f : X → Y} {s : Set X}

/-- **The far side of a shrinking circular cut keeps a fixed width.** Suppose the image under `f`
of the far side at radius `0`, `s \ closedBall x 0`, has at least two points, and the image of `s`
is bounded. Then there are `d > 0` and `ρ₀ > 0` such that

> `d ≤ diam (f '' (s \ closedBall x ρ))` for every `ρ ≤ ρ₀`.

In a metric space `s \ closedBall x 0 = s \ {x}`, so when `x ∉ s` the first hypothesis just asks
that `f '' s` have two points. No hypothesis relates `f` to the metric of `X`. -/
theorem exists_pos_forall_le_diam_image_sdiff_closedBall
    (hfs : (f '' (s \ closedBall x 0)).Nontrivial) (hb : Bornology.IsBounded (f '' s)) :
    ∃ d > 0, ∃ ρ₀ > 0, ∀ ρ ≤ ρ₀, d ≤ diam (f '' (s \ closedBall x ρ)) := by
  obtain ⟨_, ⟨z₁, ⟨hz₁, h₁⟩, rfl⟩, _, ⟨z₂, ⟨hz₂, h₂⟩, rfl⟩, hne⟩ := hfs
  rw [mem_closedBall, not_le] at h₁ h₂
  refine ⟨dist (f z₁) (f z₂), dist_pos.mpr hne, min (dist z₁ x) (dist z₂ x) / 2,
    half_pos (lt_min h₁ h₂), fun ρ hρ => ?_⟩
  have hmem {z} (hz : z ∈ s) (hzd : min (dist z₁ x) (dist z₂ x) ≤ dist z x) :
      f z ∈ f '' (s \ closedBall x ρ) :=
    mem_image_of_mem f ⟨hz, by rw [mem_closedBall, not_le]; linarith [lt_min h₁ h₂]⟩
  exact dist_le_diam_of_mem (hb.subset (image_mono sdiff_subset))
    (hmem hz₁ (min_le_left _ _)) (hmem hz₂ (min_le_right _ _))

end TauCeti
