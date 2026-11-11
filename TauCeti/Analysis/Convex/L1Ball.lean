/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Convex.Gauge

/-!
# The finite-dimensional ℓ¹ unit ball

The set `l1Ball ι` is the closed ℓ¹ unit ball on `ι → ℝ`, equipped with its usual supremum
norm and product volume. It is a compact, symmetric, convex neighborhood of zero, its gauge
is the sum of the absolute coordinates, and its volume is `2 ^ n / n!`, where `n` is the
cardinality of `ι`. The statements include the empty index type.

These facts provide a convex body for lattice estimates in coordinate spaces, including
the logarithmic space of a number field. The geometry uses Mathlib's `PiLp` closed ball;
the volume specializes `MeasureTheory.volume_sum_rpow_le` to exponent one.
-/

public noncomputable section

open MeasureTheory
open scoped Pointwise Topology

namespace TauCeti

variable (ι : Type*) [Fintype ι]

/-- The closed ℓ¹ unit ball in a finite real coordinate space. -/
def l1Ball : Set (ι → ℝ) := {x | ∑ i, |x i| ≤ 1}

/-- Membership in the ℓ¹ unit ball is a bound on the sum of absolute coordinates. -/
@[simp]
theorem mem_l1Ball (x : ι → ℝ) : x ∈ l1Ball ι ↔ ∑ i, |x i| ≤ 1 := (Iff.rfl)

private theorem l1Ball_eq_preimage_closedBall :
    l1Ball ι = (WithLp.toLp 1) ⁻¹' Metric.closedBall
      (0 : PiLp 1 (fun _ : ι ↦ ℝ)) 1 := by
  ext x
  simp [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_of_L1, Real.norm_eq_abs]

/-- The ℓ¹ unit ball is convex. -/
theorem convex_l1Ball : Convex ℝ (l1Ball ι) := by
  rw [l1Ball_eq_preimage_closedBall]
  exact (convex_closedBall _ _).linear_preimage
    (WithLp.linearEquiv 1 ℝ (ι → ℝ)).symm.toLinearMap

/-- The ℓ¹ unit ball is symmetric about zero. -/
theorem neg_mem_l1Ball (x : ι → ℝ) : -x ∈ l1Ball ι ↔ x ∈ l1Ball ι := by
  simp

/-- The ℓ¹ unit ball is compact, including in dimension zero. -/
theorem isCompact_l1Ball : IsCompact (l1Ball ι) := by
  rw [l1Ball_eq_preimage_closedBall]
  exact (PiLp.continuousLinearEquiv 1 ℝ (fun _ : ι ↦ ℝ)).symm.toHomeomorph.isCompact_preimage.mpr
    (isCompact_closedBall _ _)

/-- The ℓ¹ unit ball is closed. -/
theorem isClosed_l1Ball : IsClosed (l1Ball ι) :=
  (isCompact_l1Ball ι).isClosed

/-- The ℓ¹ unit ball is bounded in the ambient supremum norm. -/
theorem isBounded_l1Ball : Bornology.IsBounded (l1Ball ι) :=
  (isCompact_l1Ball ι).isBounded

/-- Zero is an interior point of the ℓ¹ unit ball. -/
theorem zero_mem_interior_l1Ball : (0 : ι → ℝ) ∈ interior (l1Ball ι) := by
  rw [mem_interior_iff_mem_nhds, l1Ball_eq_preimage_closedBall]
  refine (PiLp.continuous_toLp 1 _).continuousAt.preimage_mem_nhds ?_
  rw [WithLp.toLp_zero]
  exact Metric.closedBall_mem_nhds 0 one_pos

/-- The ℓ¹ unit ball absorbs every vector. -/
theorem absorbent_l1Ball : Absorbent ℝ (l1Ball ι) :=
  absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp (zero_mem_interior_l1Ball ι))

/-- The gauge of the ℓ¹ unit ball is the sum of absolute coordinates. -/
theorem gauge_l1Ball (x : ι → ℝ) : gauge (l1Ball ι) x = ∑ i, |x i| := by
  -- Transport along `WithLp.toLp 1`, the linear equivalence `(WithLp.linearEquiv 1 ℝ _).symm`:
  -- the gauge of the preimage ball at `x` is the gauge of the `PiLp 1` closed ball at `toLp 1 x`.
  have hg : gauge (l1Ball ι) x =
      gauge (Metric.closedBall (0 : PiLp 1 (fun _ : ι ↦ ℝ)) 1) (WithLp.toLp 1 x) := by
    rw [l1Ball_eq_preimage_closedBall, ← WithLp.coe_symm_linearEquiv 1 ℝ (ι → ℝ)]
    exact (WithLp.linearEquiv 1 ℝ (ι → ℝ)).symm.toLinearMap.gauge_preimage _ x
  -- The `PiLp 1` norm of `toLp 1 x` is the sum of the absolute coordinates of `x`.
  rw [hg, gauge_closedBall zero_le_one, div_one, PiLp.norm_eq_of_L1]
  simp

/-- The ℓ¹ unit ball has volume `2 ^ n / n!` in dimension `n`, also when `n = 0`. -/
theorem volume_l1Ball :
    volume (l1Ball ι) = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  cases isEmpty_or_nonempty ι with
  | inl h => simp [Measure.volume_pi_eq_dirac (0 : ι → ℝ)]
  | inr h =>
    simpa [← mem_l1Ball, Real.Gamma_nat_eq_factorial, one_add_one_eq_two] using
      volume_sum_rpow_le (ι := ι) (p := 1) le_rfl 1

end TauCeti
