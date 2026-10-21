/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# The sup norm and distance over a one-point index type

A product of seminormed groups over a one-point index type carries the sup norm of its only
coordinate: `Pi.norm_unique` and `Pi.nnnorm_unique` (with multiplicative forms `Pi.norm_unique'`
and `Pi.nnnorm_unique'`). This is the norm counterpart of `IsometryEquiv.funUnique`, and it
identifies, for example, the norm of `x : Fin 1 → ℝ` with `|x 0|`.

Likewise, for a product of pseudometric spaces over a one-point index type, the sup distance is the
distance of the only coordinates (`Pi.dist_unique`), so balls, closed balls and spheres are
detected on that coordinate (`Pi.mem_ball_unique`, `Pi.mem_closedBall_unique` and
`Pi.mem_sphere_unique`).
-/

public section

variable {ι : Type*} {G : ι → Type*} [Fintype ι] [Unique ι] [∀ i, SeminormedGroup (G i)]

/-- Over a one-point index type, the sup norm is the norm of the only coordinate. -/
@[to_additive (attr := simp) Pi.nnnorm_unique
  /-- Over a one-point index type, the sup norm is the norm of the only coordinate. -/]
lemma Pi.nnnorm_unique' (f : ∀ i, G i) : ‖f‖₊ = ‖f default‖₊ := by
  rw [Pi.nnnorm_def', Finset.univ_unique, Finset.sup_singleton]

/-- Over a one-point index type, the sup norm is the norm of the only coordinate. -/
@[to_additive (attr := simp) Pi.norm_unique
  /-- Over a one-point index type, the sup norm is the norm of the only coordinate. -/]
lemma Pi.norm_unique' (f : ∀ i, G i) : ‖f‖ = ‖f default‖ :=
  congrArg NNReal.toReal (Pi.nnnorm_unique' f)

section Metric

open Metric

variable {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]

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

/-- Over a one-point index type, a sphere is the sphere around the only coordinate. -/
lemma Pi.mem_sphere_unique {f g : ∀ i, X i} {r : ℝ} :
    f ∈ sphere g r ↔ f default ∈ sphere (g default) r := by
  rw [mem_sphere, mem_sphere, Pi.dist_unique]

end Metric
