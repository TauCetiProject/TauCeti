/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The logarithmic ℓ¹ ball

The closed ℓ¹ unit ball in the logarithmic space of a number field is a compact, symmetric,
convex neighborhood of zero. Its gauge is the sum of the absolute values of the coordinates,
and its volume in unit rank `r` is `2 ^ r / r!`, including rank zero.

Together with the height comparison for the logarithmic embedding, this ball lets geometry of
numbers produce fundamental units with a bounded product of heights. The norm on Mathlib's
`logSpace` is the supremum norm, so this ball is not its metric unit ball. We use Mathlib's
`PiLp` closed ball for the geometry and `MeasureTheory.volume_sum_rpow_le` for its volume.

## References

* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3, Lemma 1.
-/

public noncomputable section

open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Pointwise Topology

namespace TauCeti.NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- The closed ℓ¹ unit ball in the logarithmic space of a number field. -/
def logBall : Set (logSpace K) := {x | ∑ w, |x w| ≤ 1}

open Classical in
/-- Membership in the logarithmic ball is the ℓ¹ bound on the coordinates. -/
@[simp]
theorem mem_logBall (x : logSpace K) : x ∈ logBall K ↔ ∑ w, |x w| ≤ 1 :=
  Iff.rfl

open Classical in
private theorem logBall_eq_preimage_closedBall :
    logBall K = (WithLp.toLp 1) ⁻¹' Metric.closedBall
      (0 : PiLp 1 (fun _ : {w : InfinitePlace K // w ≠ w₀} ↦ ℝ)) 1 := by
  ext x
  simp [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_of_L1, Real.norm_eq_abs]

/-- The logarithmic ball is convex. -/
theorem convex_logBall : Convex ℝ (logBall K) := by
  classical
  rw [logBall_eq_preimage_closedBall]
  exact (convex_closedBall _ _).linear_preimage
    (WithLp.linearEquiv 1 ℝ (logSpace K)).symm.toLinearMap

/-- The logarithmic ball is symmetric about zero. -/
theorem neg_mem_logBall (x : logSpace K) : -x ∈ logBall K ↔ x ∈ logBall K := by
  classical
  simp

/-- The logarithmic ball is compact, also when the unit rank is zero. -/
theorem isCompact_logBall : IsCompact (logBall K) := by
  classical
  rw [logBall_eq_preimage_closedBall]
  exact (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : {w : InfinitePlace K // w ≠ w₀} ↦ ℝ)).symm.toHomeomorph.isCompact_preimage.mpr
      (isCompact_closedBall _ _)

/-- The logarithmic ball is closed. -/
theorem isClosed_logBall : IsClosed (logBall K) :=
  (isCompact_logBall K).isClosed

open Classical in
/-- The logarithmic ball is bounded in the supremum norm on `logSpace K`. -/
theorem isBounded_logBall : Bornology.IsBounded (logBall K) :=
  (isCompact_logBall K).isBounded

/-- Zero is an interior point of the logarithmic ball. -/
theorem zero_mem_interior_logBall : (0 : logSpace K) ∈ interior (logBall K) := by
  classical
  have hopen : IsOpen {x : logSpace K | ∑ w, |x w| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  exact mem_interior_iff_mem_nhds.mpr <|
    Filter.mem_of_superset (hopen.mem_nhds (by simp)) (fun x hx ↦ (mem_logBall K x).mpr hx.le)

/-- The logarithmic ball absorbs every vector in the logarithmic space. -/
theorem absorbent_logBall : Absorbent ℝ (logBall K) :=
  absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp (zero_mem_interior_logBall K))

open Classical in
/-- The gauge of the logarithmic ball is the ℓ¹ norm, rather than the ambient supremum norm. -/
theorem gauge_logBall (x : logSpace K) : gauge (logBall K) x = ∑ w, |x w| := by
  let y := WithLp.toLp 1 x
  have hg : gauge (logBall K) x = gauge (Metric.closedBall (0 : PiLp 1
      (fun _ : {w : InfinitePlace K // w ≠ w₀} ↦ ℝ)) 1) y := by
    rw [gauge_def', gauge_def']
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq, mem_logBall, Metric.mem_closedBall, dist_zero_right,
      PiLp.norm_eq_of_L1, PiLp.smul_apply, Pi.smul_apply, Real.norm_eq_abs,
      smul_eq_mul, y]
  rw [hg, gauge_closedBall zero_le_one, div_one, PiLp.norm_eq_of_L1]
  simp [y, Real.norm_eq_abs]

open Classical in
/-- The logarithmic ball has volume `2 ^ r / r!` in unit rank `r`. In rank zero its volume is
one, the volume of the whole zero-dimensional logarithmic space. -/
theorem volume_logBall :
    volume (logBall K) = ENNReal.ofReal ((2 : ℝ) ^ rank K / (rank K).factorial) := by
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = rank K := by
    rw [← Module.finrank_fintype_fun_eq_card (R := ℝ),
      NumberField.Units.finrank_eq_rank]
  cases isEmpty_or_nonempty {w : InfinitePlace K // w ≠ w₀} with
  | inl h =>
    have hr : rank K = 0 := by simpa using hcard.symm
    have hb : logBall K = Set.univ := by ext x; simp
    rw [hb, MeasureTheory.Measure.volume_pi_eq_dirac (0 : logSpace K)]
    simp [hr]
  | inr h =>
    simpa [logBall, Real.Gamma_nat_eq_factorial, hcard, one_add_one_eq_two] using
      (MeasureTheory.volume_sum_rpow_le
        (ι := {w : InfinitePlace K // w ≠ w₀}) (p := 1) le_rfl 1)

end TauCeti.NumberField.Units
