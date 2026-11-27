/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.EssentialBoundary.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.InnerProductSpace.Euclidean.RationalPoints
import TauCeti.Analysis.Normed.Affine.AddTorsor.TangentBall

/-!
# The essential boundary of a ball

Against an additive Haar measure on a finite-dimensional real normed space, the essential boundary
of the open ball `ball c r`, `r ≠ 0`, is the sphere `sphere c r`
(`TauCeti.essentialBoundary_ball`): interior points of the ball and points outside the closed ball
have density `1` and `0`, while at a point `x` of the sphere both the ball and its complement
contain a ball of radius `ρ / 2` inside `ball x ρ`, so the density of the ball at `x` is neither
`0` nor `1`.

The essential boundary only depends on the set up to null sets, so the punctured ball
`ball c r \ {c}` and, in `EuclideanSpace ℝ (Fin n)`, the union of `ball c r` with the countable set
of points with rational coordinates (`TauCeti.EuclideanSpace.rationalPoints`, a null dense set),
also have essential boundary `sphere c r`, although their frontiers are larger: unlike the
frontier, the essential boundary ignores null sets.
-/

public section

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The essential boundary of a ball is its sphere.** For `r ≠ 0`, the open ball `ball c r` has
essential boundary `sphere c r`. -/
theorem essentialBoundary_ball {c : E} {r : ℝ} (hr : r ≠ 0) :
    essentialBoundary μ (ball c r) = sphere c r := by
  refine (essentialBoundary_subset_frontier.trans (frontier_ball c hr).subset).antisymm
    fun x hx ↦ ?_
  rw [mem_sphere] at hx
  -- The sphere is empty for `r < 0`, so `r > 0` here.
  replace hr : 0 < r := (hx ▸ dist_nonneg).lt_of_ne' hr
  have hball : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall x ρ) ≠ 0 ∧ μ (closedBall x ρ) ≠ ∞ :=
    eventually_mem_nhdsWithin.mono fun ρ (hρ : 0 < ρ) ↦
      ⟨(measure_closedBall_pos μ x hρ).ne', measure_closedBall_lt_top.ne⟩
  have hnm := (measurableSet_ball (x := c) (ε := r)).nullMeasurableSet (μ := μ)
  refine mem_essentialBoundary.2 ⟨fun h1 ↦ ?_, fun h0 ↦ ?_⟩
  · -- Outside: the ball of radius `ρ / 2` about `x - (ρ / 2r)(c - x)` misses `ball c r`.
    refine not_hasDensityAt_zero_of_eventually_exists_ball_subset ?_
      ((hasDensityAt_compl_zero_iff hnm hball).2 (mem_essentialInterior.1 h1))
    filter_upwards with ρ
    have h := ball_lineMap_neg_subset_compl_ball_inter_ball (δ := ρ / 2) hx hr
    rw [two_mul, add_halves] at h
    exact ⟨_, h⟩
  · -- Inside: the ball of radius `ρ / 2` about `x + (ρ / 2r)(c - x)` lies in `ball c r`.
    refine not_hasDensityAt_zero_of_eventually_exists_ball_subset ?_ (mem_essentialExterior.1 h0)
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ ⟨_, hρr⟩
    have h := ball_lineMap_subset_ball_inter_ball (δ := ρ / 2) hx (by linarith)
    rw [two_mul, add_halves] at h
    exact ⟨_, h⟩

/-- The punctured ball `ball c r \ {c}`, `r ≠ 0`, has essential boundary `sphere c r`. -/
theorem essentialBoundary_ball_sdiff_singleton [Nontrivial E] {c : E} {r : ℝ} (hr : r ≠ 0) :
    essentialBoundary μ (ball c r \ {c}) = sphere c r := by
  rw [essentialBoundary_congr_ae (sdiff_null_ae_eq_self (measure_singleton c)),
    essentialBoundary_ball hr]

/-- In `EuclideanSpace ℝ (Fin n)`, the union of the ball `ball c r`, `r ≠ 0`, with the points of
rational coordinates has essential boundary `sphere c r`. -/
theorem essentialBoundary_ball_union_rational {n : ℕ} [NeZero n]
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : r ≠ 0) :
    essentialBoundary volume (ball c r ∪ EuclideanSpace.rationalPoints n) = sphere c r := by
  rw [essentialBoundary_congr_ae (union_ae_eq_left_of_ae_eq_empty
    (ae_eq_empty.2 EuclideanSpace.volume_rationalPoints)), essentialBoundary_ball hr]

end TauCeti
