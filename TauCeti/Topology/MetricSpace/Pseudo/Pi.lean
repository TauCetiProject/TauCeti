/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The sup distance on finite products

For a product of pseudometric spaces over a one-point index type, the sup distance is the
distance of the only coordinates (`Pi.dist_unique`), so balls, closed balls and spheres are
detected on that coordinate (`Pi.mem_ball_unique`, `Pi.mem_closedBall_unique` and
`Pi.mem_sphere_unique`), and balls and closed balls are preimages under evaluation at that
coordinate (`Pi.ball_unique` and `Pi.closedBall_unique`). This is the pointwise form of
`IsometryEquiv.funUnique`, stated for dependent families.

Over any finite index type, the sup distance controls weighted sums of squared coordinate
distances `∑ᵢ wᵢ dist(xᵢ, pᵢ)²` with nonnegative weights: outside the ball of nonnegative radius
`ρ` around `p` such a sum is at least `c ρ²` for any common lower bound `c` of the weights
(`TauCeti.mul_sq_le_sum_mul_dist_sq_of_notMem_ball`), and on the closed ball of radius `δ` it is
at most `(∑ᵢ wᵢ) δ²` (`TauCeti.sum_mul_dist_sq_le_mul_sq_of_mem_closedBall`). On `ι → ℝ` these
are the weighted sums of squares `∑ᵢ wᵢ (xᵢ - pᵢ)²`, by `Real.dist_eq` and `sq_abs`.

Over a finite index type, the product of the balls of radii `r i` around `c i` is the increasing
union of the concentric product balls of radii `r i - 1 / (k + 1)`
(`TauCeti.exists_polyradius_exhaustion`).
-/

public section

open Metric

variable {ι : Type*} {X : ι → Type*} [Fintype ι] [∀ i, PseudoMetricSpace (X i)]

section Unique

variable [Unique ι]

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

variable {w : ι → ℝ} {x p : ∀ i, X i}

/-- Outside the ball of nonnegative radius `ρ` around `p`, a weighted sum of squared coordinate
distances `∑ᵢ wᵢ dist(xᵢ, pᵢ)²` with nonnegative weights `wᵢ ≥ c` is at least `c ρ²`. -/
theorem mul_sq_le_sum_mul_dist_sq_of_notMem_ball {c ρ : ℝ} (hρ : 0 ≤ ρ) (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ i, c ≤ w i) (hx : x ∉ ball p ρ) :
    c * ρ ^ 2 ≤ ∑ i, w i * dist (x i) (p i) ^ 2 := by
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ w j * dist (x j) (p j) ^ 2 :=
    fun j _ ↦ mul_nonneg (hw j) (sq_nonneg _)
  obtain rfl | hρ := hρ.eq_or_lt
  · rw [zero_pow two_ne_zero, mul_zero]
    exact Finset.sum_nonneg hnn
  rw [mem_ball, dist_pi_lt_iff hρ] at hx
  simp only [not_forall, not_lt] at hx
  obtain ⟨i, hi⟩ := hx
  calc c * ρ ^ 2 ≤ w i * dist (x i) (p i) ^ 2 :=
        mul_le_mul (hc i) (pow_le_pow_left₀ hρ.le hi 2) (sq_nonneg _) (hw i)
    _ ≤ ∑ j, w j * dist (x j) (p j) ^ 2 :=
        Finset.single_le_sum (f := fun j ↦ w j * dist (x j) (p j) ^ 2) hnn (Finset.mem_univ i)

/-- On the closed ball of radius `δ` around `p`, a weighted sum of squared coordinate distances
`∑ᵢ wᵢ dist(xᵢ, pᵢ)²` with nonnegative weights is at most `(∑ᵢ wᵢ) δ²`. -/
theorem sum_mul_dist_sq_le_mul_sq_of_mem_closedBall {δ : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hx : x ∈ closedBall p δ) :
    ∑ i, w i * dist (x i) (p i) ^ 2 ≤ (∑ i, w i) * δ ^ 2 := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (hw i)
  exact pow_le_pow_left₀ dist_nonneg ((dist_le_pi_dist x p i).trans (mem_closedBall.1 hx)) 2

omit [Fintype ι] in
/-- There are polyradii `s k` with `s k i < r i` (namely `s k i = r i - 1 / (k + 1)`) that
increase strictly in `k`, so the concentric product balls of radii `s k i` around `c` form an
increasing family exhausting the product of the balls of radii `r i`. -/
theorem exists_polyradius_exhaustion [Finite ι] (c : ∀ i, X i) (r : ι → ℝ) :
    ∃ s : ℕ → ι → ℝ, (∀ k i, s k i < s (k + 1) i) ∧ Monotone s ∧ (∀ k i, s k i < r i) ∧
      ∀ z ∈ Set.univ.pi fun i ↦ ball (c i) (r i),
        ∃ k, z ∈ Set.univ.pi fun i ↦ ball (c i) (s k i) := by
  refine ⟨fun k i ↦ r i - 1 / ((k : ℝ) + 1), fun k i ↦ ?_, fun m k hmk i ↦ ?_, fun k i ↦ ?_,
    fun z hz ↦ ?_⟩
  · exact sub_lt_sub_left (by exact_mod_cast Nat.one_div_lt_one_div (Nat.lt_succ_self k)) _
  · exact sub_le_sub_left (Nat.one_div_le_one_div hmk) _
  · exact sub_lt_self _ Nat.one_div_pos_of_nat
  · have h (i : ι) : ∀ᶠ k : ℕ in Filter.atTop, dist (z i) (c i) < r i - 1 / ((k : ℝ) + 1) := by
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hz i (Set.mem_univ i)))
      exact Filter.eventually_atTop.2 ⟨n, fun k hk ↦
        lt_sub_comm.1 ((Nat.one_div_le_one_div hk).trans_lt hn)⟩
    obtain ⟨k, hk⟩ := (Filter.eventually_all.2 h).exists
    exact ⟨k, fun i _ ↦ hk i⟩

end TauCeti
