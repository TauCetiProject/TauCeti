/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

/-!
# Fibrewise sums of Euclidean coordinates

A map `f : ι → κ` of finite index types coarsens a Euclidean coordinate system: the coordinates
of a vector indexed by `ι` are merged into the groups cut out by the fibres of `f`, one group
summed into each coordinate of a vector indexed by `κ`.  This is Mathlib's `FunOnFinite.map`,
here read through `EuclideanSpace.equiv` so that it acts on Euclidean space, where it is again
continuous and measurable. The coordinates may be real or complex; measurability uses the
Borel measurable structure on the scalar field.

## Main definitions

* `TauCeti.euclideanFiberSum` sums the coordinates of a Euclidean vector over each fibre of a map
  of index types.

The Euclidean norm bounds the sum of coordinate norms by the square root of the number of
coordinates. This finite-dimensional Cauchy--Schwarz estimate also controls matrix actions
from entrywise bounds. In the same way the Euclidean distance is at most `√n` times the sup
distance of the coordinate vectors, which places cubes inside Euclidean balls.

## Additional result

* `EuclideanSpace.sum_norm_le_sqrt_card_mul_norm`: the sum of coordinate norms is at most the
  square root of the coordinate count times the Euclidean norm.
* `EuclideanSpace.dist_le_sqrt_card_mul_dist_ofLp`: the Euclidean distance is at most `√n` times
  the sup distance of the coordinate vectors.
* `EuclideanSpace.preimage_ofLp_closedBall_subset_closedBall`,
  `EuclideanSpace.preimage_ofLp_ball_subset_ball`: a cube of half-side `r` lies in the
  concentric Euclidean ball of radius `√n * r`.
* `EuclideanSpace.closedBall_subset_preimage_ofLp_closedBall`: a Euclidean ball of radius `r`
  lies in the concentric cube of half-side `r`.

## Source

The coordinate-norm estimate is adapted from
`ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.
-/

public section

noncomputable section

open scoped BigOperators

namespace EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/--
**`ℓ¹ ≤ √card · ℓ²` on Euclidean space.** For `x : EuclideanSpace 𝕜 ι`,
`∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖`.
-/
theorem sum_norm_le_sqrt_card_mul_norm
    (x : EuclideanSpace 𝕜 ι) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
    simpa [Finset.card_univ] using
      sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖x i‖)
  have hnorm : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have hsum_nonneg : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hrhs_nonneg : 0 ≤ Real.sqrt (Fintype.card ι) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq : (∑ i, ‖x i‖) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 := by
    have hrw : (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 = (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card ι : ℝ))]
    rw [hrw, hnorm]; exact hcs
  exact (abs_le_of_sq_le_sq' hsq hrhs_nonneg).2

/-- The Euclidean distance between two points is at most the square root of the coordinate count
times the sup distance between their coordinate vectors. -/
theorem dist_le_sqrt_card_mul_dist_ofLp (x y : EuclideanSpace 𝕜 ι) :
    dist x y ≤ Real.sqrt (Fintype.card ι) * dist (WithLp.ofLp x) (WithLp.ofLp y) := by
  have h := (PiLp.lipschitzWith_toLp 2 (fun _ : ι => 𝕜)).dist_le_mul (WithLp.ofLp x)
    (WithLp.ofLp y)
  have hc : (((Fintype.card ι : NNReal) ^ (1 / (2 : ENNReal)).toReal : NNReal) : ℝ) =
      Real.sqrt (Fintype.card ι) := by
    rw [NNReal.coe_rpow, NNReal.coe_natCast, Real.sqrt_eq_rpow]
    norm_num
  rwa [hc, WithLp.toLp_ofLp, WithLp.toLp_ofLp] at h

/-- The cube of half-side `r` about `ofLp x` lies in the Euclidean ball of radius `√n * r`
about `x`. -/
theorem preimage_ofLp_closedBall_subset_closedBall (x : EuclideanSpace 𝕜 ι) (r : ℝ) :
    WithLp.ofLp ⁻¹' Metric.closedBall (WithLp.ofLp x) r ⊆
      Metric.closedBall x (Real.sqrt (Fintype.card ι) * r) := fun y hy =>
  (dist_le_sqrt_card_mul_dist_ofLp y x).trans
    (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))

/-- The open cube of half-side `r` about `ofLp x` lies in the open Euclidean ball of radius
`√n * r` about `x`. -/
theorem preimage_ofLp_ball_subset_ball [Nonempty ι] (x : EuclideanSpace 𝕜 ι) (r : ℝ) :
    WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp x) r ⊆
      Metric.ball x (Real.sqrt (Fintype.card ι) * r) := fun y hy =>
  (dist_le_sqrt_card_mul_dist_ofLp y x).trans_lt
    (mul_lt_mul_of_pos_left hy (Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)))

/-- The closed Euclidean ball of radius `r` about `x` lies in the cube of half-side `r` about
`ofLp x`. -/
theorem closedBall_subset_preimage_ofLp_closedBall (x : EuclideanSpace 𝕜 ι) (r : ℝ) :
    Metric.closedBall x r ⊆ WithLp.ofLp ⁻¹' Metric.closedBall (WithLp.ofLp x) r := fun y hy => by
  have h := (PiLp.lipschitzWith_ofLp 2 (fun _ : ι => 𝕜)).dist_le_mul y x
  rw [NNReal.coe_one, one_mul] at h
  exact h.trans hy

end EuclideanSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Sum the coordinates of a Euclidean vector over each fibre of `f`.

This is Mathlib's `FunOnFinite.map` read in Euclidean coordinates. -/
def euclideanFiberSum (f : ι → κ) (x : EuclideanSpace 𝕜 ι) : EuclideanSpace 𝕜 κ :=
  (EuclideanSpace.equiv κ 𝕜).symm (FunOnFinite.map f (EuclideanSpace.equiv ι 𝕜 x))

@[simp]
theorem euclideanFiberSum_apply [DecidableEq κ] (f : ι → κ) (x : EuclideanSpace 𝕜 ι) (j : κ) :
    euclideanFiberSum f x j = ∑ i with f i = j, x i := by
  simp [euclideanFiberSum, FunOnFinite.map_apply_apply]

/-- Fibrewise summation is continuous. -/
@[fun_prop]
theorem continuous_euclideanFiberSum (f : ι → κ) :
    Continuous (euclideanFiberSum (𝕜 := 𝕜) (ι := ι) f) :=
  (EuclideanSpace.equiv κ 𝕜).symm.continuous.comp <|
    (FunOnFinite.continuous_map 𝕜 f).comp (EuclideanSpace.equiv ι 𝕜).continuous

/-- Fibrewise summation is measurable. -/
@[fun_prop]
theorem measurable_euclideanFiberSum [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : ι → κ) :
    Measurable (euclideanFiberSum (𝕜 := 𝕜) (ι := ι) f) :=
  (continuous_euclideanFiberSum (𝕜 := 𝕜) f).measurable

end TauCeti
