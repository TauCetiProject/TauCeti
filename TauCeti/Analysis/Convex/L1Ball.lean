/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

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
  have hopen : IsOpen {x : ι → ℝ | ∑ i, |x i| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  exact mem_interior_iff_mem_nhds.mpr <|
    Filter.mem_of_superset (hopen.mem_nhds (by simp)) (fun x hx ↦ (mem_l1Ball ι x).mpr hx.le)

/-- The ℓ¹ unit ball absorbs every vector. -/
theorem absorbent_l1Ball : Absorbent ℝ (l1Ball ι) :=
  absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp (zero_mem_interior_l1Ball ι))

/-- The gauge of the ℓ¹ unit ball is the sum of absolute coordinates. -/
theorem gauge_l1Ball (x : ι → ℝ) : gauge (l1Ball ι) x = ∑ i, |x i| := by
  rw [l1Ball_eq_preimage_closedBall]
  have hg : gauge ((WithLp.toLp 1) ⁻¹' Metric.closedBall
      (0 : PiLp 1 (fun _ : ι ↦ ℝ)) 1) x =
      gauge (Metric.closedBall (0 : PiLp 1 (fun _ : ι ↦ ℝ)) 1) (WithLp.toLp 1 x) := by
    simp only [gauge_def', Set.mem_preimage, WithLp.toLp_smul]
  rw [hg, gauge_closedBall zero_le_one, div_one, PiLp.norm_eq_of_L1]
  simp [Real.norm_eq_abs]

/-- The ℓ¹ unit ball has volume `2 ^ n / n!` in dimension `n`, also when `n = 0`. -/
theorem volume_l1Ball :
    volume (l1Ball ι) = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have hb : l1Ball ι = Set.univ := by ext x; simp
    rw [hb, MeasureTheory.Measure.volume_pi_eq_dirac (0 : ι → ℝ)]
    simp
  | inr h =>
    have hb : l1Ball ι = {x : ι → ℝ | (∑ i, |x i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ 1} := by
      ext x
      simp
    rw [hb]
    -- The ambient space is the pi type `ι → ℝ`, so its volume is the product volume.
    simpa [Real.Gamma_nat_eq_factorial, one_add_one_eq_two] using
      (MeasureTheory.volume_sum_rpow_le (ι := ι) (p := 1) le_rfl 1)

end TauCeti
