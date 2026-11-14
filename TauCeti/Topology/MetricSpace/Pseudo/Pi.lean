/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The sup distance over one-point and disjoint-union index types

For a product of pseudometric spaces over a one-point index type, the sup distance is the
distance of the only coordinates (`Pi.dist_unique`), so balls, closed balls and spheres are
detected on that coordinate (`Pi.mem_ball_unique`, `Pi.mem_closedBall_unique` and
`Pi.mem_sphere_unique`), and balls and closed balls are preimages under evaluation at that
coordinate (`Pi.ball_unique` and `Pi.closedBall_unique`). This is the pointwise form of
`IsometryEquiv.funUnique`, stated for dependent families.

Over a disjoint union `ι ⊕ ι'` of finite index types, the sup distance of `Sum.elim` is the maximum
of the sup distances on the two summands (`Pi.nndist_sumElim`, `Pi.dist_sumElim`), so membership in
an open sup-norm ball splits across the two summands (`Pi.sumElim_mem_ball`).
-/

public section

open Metric

section Unique

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

/-- Over a one-point index type, a closed ball is the closed ball around the only coordinate. -/
lemma Pi.closedBall_unique (g : ∀ i, X i) (r : ℝ) :
    closedBall g r = Function.eval default ⁻¹' closedBall (g default) r :=
  Set.ext fun _ ↦ Pi.mem_closedBall_unique

/-- Over a one-point index type, a sphere is the sphere around the only coordinate. -/
lemma Pi.mem_sphere_unique {f g : ∀ i, X i} {r : ℝ} :
    f ∈ sphere g r ↔ f default ∈ sphere (g default) r := by
  rw [mem_sphere, mem_sphere, Pi.dist_unique]

end Unique

section SumElim

variable {ι ι' X : Type*} [Fintype ι] [Fintype ι'] [PseudoMetricSpace X]

/-- On a disjoint union of finite index types, the sup `nndist` is the maximum of the sup `nndist`s
on the two summands. -/
@[simp]
lemma Pi.nndist_sumElim (f₁ f₂ : ι → X) (g₁ g₂ : ι' → X) :
    nndist (Sum.elim f₁ g₁) (Sum.elim f₂ g₂) = max (nndist f₁ f₂) (nndist g₁ g₂) := by
  simp [nndist_pi_def, ← Finset.univ_disjSum_univ, Finset.sup_disjSum]

/-- On a disjoint union of finite index types, the sup distance is the maximum of the sup distances
on the two summands. -/
@[simp]
lemma Pi.dist_sumElim (f₁ f₂ : ι → X) (g₁ g₂ : ι' → X) :
    dist (Sum.elim f₁ g₁) (Sum.elim f₂ g₂) = max (dist f₁ f₂) (dist g₁ g₂) := by
  simp only [dist_nndist, Pi.nndist_sumElim, NNReal.coe_max]

/-- Membership of `Sum.elim f₁ g₁` in an open sup-norm ball around `Sum.elim f₂ g₂` splits across
the two summands. -/
lemma Pi.sumElim_mem_ball {f₁ f₂ : ι → X} {g₁ g₂ : ι' → X} {r : ℝ} :
    Sum.elim f₁ g₁ ∈ ball (Sum.elim f₂ g₂) r ↔ f₁ ∈ ball f₂ r ∧ g₁ ∈ ball g₂ r := by
  rw [mem_ball, mem_ball, mem_ball, Pi.dist_sumElim, max_lt_iff]

end SumElim
