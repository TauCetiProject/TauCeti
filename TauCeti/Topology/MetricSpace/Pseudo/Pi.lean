/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The sup distance on finite products

For a product of pseudometric spaces over a one-point index type, the sup distance is the
distance of the only coordinates (`Pi.dist_unique`), so balls, closed balls and spheres are
detected on that coordinate (`Pi.mem_ball_unique`, `Pi.mem_closedBall_unique` and
`Pi.mem_sphere_unique`), and balls and closed balls are preimages under evaluation at that
coordinate (`Pi.ball_unique` and `Pi.closedBall_unique`). This is the pointwise form of
`IsometryEquiv.funUnique`, stated for dependent families.

On `ι → ℝ` with `ι` finite, the sup distance controls weighted sums of squares
`∑ᵢ wᵢ (xᵢ - pᵢ)²` with nonnegative weights: outside the ball of radius `ρ` around `p` such a sum
is at least `(minᵢ wᵢ) ρ²` (`TauCeti.mul_sq_le_sum_mul_sub_sq_of_notMem_ball`), and on the closed
ball of radius `δ` it is at most `(∑ᵢ wᵢ) δ²`
(`TauCeti.sum_mul_sub_sq_le_mul_sq_of_mem_closedBall`).
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

/-- Over a one-point index type, a closed ball is the preimage under evaluation of the closed ball
around the only coordinate. -/
lemma Pi.closedBall_unique (g : ∀ i, X i) (r : ℝ) :
    closedBall g r = Function.eval default ⁻¹' closedBall (g default) r :=
  Set.ext fun _ ↦ Pi.mem_closedBall_unique

/-- Over a one-point index type, a sphere is the sphere around the only coordinate. -/
lemma Pi.mem_sphere_unique {f g : ∀ i, X i} {r : ℝ} :
    f ∈ sphere g r ↔ f default ∈ sphere (g default) r := by
  rw [mem_sphere, mem_sphere, Pi.dist_unique]

end Unique

namespace TauCeti

variable {ι : Type*} [Fintype ι] {w p x : ι → ℝ}

/-- Outside the ball of radius `ρ` around `p`, a weighted sum of squares `∑ᵢ wᵢ (xᵢ - pᵢ)²` with
nonnegative weights `wᵢ ≥ c` is at least `c ρ²`. -/
theorem mul_sq_le_sum_mul_sub_sq_of_notMem_ball {c ρ : ℝ} (hρ : 0 < ρ) (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ i, c ≤ w i) (hx : x ∉ ball p ρ) :
    c * ρ ^ 2 ≤ ∑ i, w i * (x i - p i) ^ 2 := by
  rw [mem_ball, dist_pi_lt_iff hρ] at hx
  simp only [not_forall, not_lt] at hx
  obtain ⟨i, hi⟩ := hx
  rw [Real.dist_eq] at hi
  have hρi : ρ ^ 2 ≤ (x i - p i) ^ 2 := by
    rw [← sq_abs (x i - p i)]
    exact pow_le_pow_left₀ hρ.le hi 2
  calc c * ρ ^ 2 ≤ w i * (x i - p i) ^ 2 := mul_le_mul (hc i) hρi (sq_nonneg _) (hw i)
    _ ≤ ∑ j, w j * (x j - p j) ^ 2 :=
        Finset.single_le_sum (f := fun j ↦ w j * (x j - p j) ^ 2)
          (fun j _ ↦ mul_nonneg (hw j) (sq_nonneg _)) (Finset.mem_univ i)

/-- On the closed ball of radius `δ` around `p`, a weighted sum of squares `∑ᵢ wᵢ (xᵢ - pᵢ)²`
with nonnegative weights is at most `(∑ᵢ wᵢ) δ²`. -/
theorem sum_mul_sub_sq_le_mul_sq_of_mem_closedBall {δ : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hx : x ∈ closedBall p δ) :
    ∑ i, w i * (x i - p i) ^ 2 ≤ (∑ i, w i) * δ ^ 2 := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (hw i)
  rw [← sq_abs (x i - p i), ← Real.dist_eq]
  exact pow_le_pow_left₀ dist_nonneg ((dist_le_pi_dist x p i).trans (mem_closedBall.1 hx)) 2

end TauCeti
