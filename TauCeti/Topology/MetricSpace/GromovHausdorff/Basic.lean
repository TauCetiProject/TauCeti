/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Gromov–Hausdorff approximations

This file provides the basic approximation map associated with a sufficiently small
Gromov–Hausdorff distance between compact nonempty metric spaces.
-/

public section

open Set Metric

namespace TauCeti

open GromovHausdorff

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]

/-- If the Gromov–Hausdorff distance is less than `ε`, there is a map with distortion less
than `2ε` and `2ε`-dense image. -/
theorem exists_approximation_of_ghDist_lt {ε : ℝ} (h : ghDist X Y < ε) :
    ∃ f : X → Y, (∀ x y, |dist (f x) (f y) - dist x y| < 2 * ε) ∧
      ∀ y, ∃ x, dist (f x) y < 2 * ε := by
  classical
  let a := optimalGHInjl X Y
  let b := optimalGHInjr X Y
  have ha : Isometry a := isometry_optimalGHInjl X Y
  have hb : Isometry b := isometry_optimalGHInjr X Y
  have hH : hausdorffDist (range a) (range b) < ε := by
    rwa [hausdorffDist_optimal]
  have hfin : hausdorffEDist (range a) (range b) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range ha.continuous).isBounded (isCompact_range hb.continuous).isBounded
  have hex (x : X) : ∃ y, dist (a x) (b y) < ε := by
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ :=
      exists_dist_lt_of_hausdorffDist_lt (mem_range_self x) hH hfin
    exact ⟨y, hy⟩
  choose f hf using hex
  refine ⟨f, ?_, ?_⟩
  · intro x y
    have hh := dist_dist_dist_le (a x) (a y) (b (f x)) (b (f y))
    rw [ha.dist_eq, hb.dist_eq, Real.dist_eq, abs_sub_comm] at hh
    exact hh.trans_lt (by linarith [hf x, hf y])
  · intro y
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
      exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y) hH hfin
    refine ⟨x, ?_⟩
    calc
      dist (f x) y = dist (b (f x)) (b y) := (hb.dist_eq _ _).symm
      _ ≤ dist (b (f x)) (a x) + dist (a x) (b y) := dist_triangle _ _ _
      _ < 2 * ε := by rw [dist_comm (b (f x))]; linarith [hf x]

end TauCeti
