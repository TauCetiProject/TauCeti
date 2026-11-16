/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Closed balls and the sup distance on finite products

For a product of pseudometric spaces over a one-point index type, the sup distance is the
distance of the only coordinates (`Pi.dist_unique`), so balls, closed balls and spheres are
detected on that coordinate (`Pi.mem_ball_unique`, `Pi.mem_closedBall_unique` and
`Pi.mem_sphere_unique`), and balls and closed balls are preimages under evaluation at that
coordinate (`Pi.ball_unique` and `Pi.closedBall_unique`). This is the pointwise form of
`IsometryEquiv.funUnique`, stated for dependent families.

Over any finite index type, replacing one coordinate of a point in a closed ball by a point in the
corresponding coordinate closed ball stays in the product closed ball
(`TauCeti.update_mem_closedBall`).
-/

public section

open Metric

variable {ι : Type*} {X : ι → Type*} [Fintype ι] [Unique ι] [∀ i, PseudoMetricSpace (X i)]

/-- Over a one-point index type, the sup distance is the distance of the only coordinates. -/
@[simp]
lemma Pi.dist_unique (f g : ∀ i, X i) : dist f g = dist (f default) (g default) := by
  rw [dist_pi_def, Finset.univ_unique, Finset.sup_singleton, coe_nndist]

/-- Over a one-point index type, a ball is the ball around the only coordinate. -/
lemma Pi.mem_ball_unique {f g : ∀ i, X i} {r : ℝ} :
    f ∈ ball g r ↔ f default ∈ ball (g default) r := by
  rw [mem_ball, mem_ball, Pi.dist_unique]

/-- Over a one-point index type, a closed ball is the closed ball around the only coordinate. -/
lemma Pi.mem_closedBall_unique {f g : ∀ i, X i} {r : ℝ} :
    f ∈ closedBall g r ↔ f default ∈ closedBall (g default) r := by
  rw [mem_closedBall, mem_closedBall, Pi.dist_unique]

/-- Over a one-point index type, a ball is the preimage under evaluation of the ball around the
only coordinate. -/
lemma Pi.ball_unique (g : ∀ i, X i) (r : ℝ) :
    ball g r = Function.eval default ⁻¹' ball (g default) r :=
  Set.ext fun _ ↦ Pi.mem_ball_unique

/-- Over a one-point index type, a closed ball is the preimage under evaluation of the closed ball
around the only coordinate. -/
lemma Pi.closedBall_unique (g : ∀ i, X i) (r : ℝ) :
    closedBall g r = Function.eval default ⁻¹' closedBall (g default) r :=
  Set.ext fun _ ↦ Pi.mem_closedBall_unique

/-- Over a one-point index type, a sphere is the sphere around the only coordinate. -/
lemma Pi.mem_sphere_unique {f g : ∀ i, X i} {r : ℝ} :
    f ∈ sphere g r ↔ f default ∈ sphere (g default) r := by
  rw [mem_sphere, mem_sphere, Pi.dist_unique]

namespace TauCeti

/-- Replacing the `i`-th coordinate of `z ∈ closedBall c R` by a point `ζ ∈ closedBall (c i) R`
stays in `closedBall c R`. -/
theorem update_mem_closedBall {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ j, PseudoMetricSpace (X j)] {c z : ∀ j, X j} {R : ℝ} {i : ι} {ζ : X i}
    (hζ : ζ ∈ closedBall (c i) R) (hz : z ∈ closedBall c R) :
    Function.update z i ζ ∈ closedBall c R := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_closedBall.mp hζ)
  rw [closedBall_pi c hR] at hz ⊢
  exact (Set.update_mem_pi_iff_of_mem hz).mpr fun _ ↦ hζ

end TauCeti
