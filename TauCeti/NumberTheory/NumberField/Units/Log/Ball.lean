/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.Analysis.Convex.L1Ball

/-!
# The logarithmic ℓ¹ ball

The closed ℓ¹ unit ball in the logarithmic space of a number field is a compact, symmetric,
convex neighborhood of zero. Its gauge is the sum of the absolute values of the coordinates,
and its volume in unit rank `r` is `2 ^ r / r!`, including rank zero.

Together with the height comparison for the logarithmic embedding, this ball lets geometry of
numbers produce fundamental units with a bounded product of heights. The norm on Mathlib's
`logSpace` is the supremum norm, so this ball is not its metric unit ball. We use the
finite-coordinate ball `TauCeti.l1Ball` for its geometry, gauge and product volume.

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
def logBall : Set (logSpace K) := l1Ball {w : InfinitePlace K // w ≠ w₀}

open Classical in
/-- Membership in the logarithmic ball is the ℓ¹ bound on the coordinates. -/
@[simp]
theorem mem_logBall (x : logSpace K) : x ∈ logBall K ↔ ∑ w, |x w| ≤ 1 :=
  mem_l1Ball _ x

open Classical in
/-- The logarithmic ball is the ℓ¹ unit ball on the coordinates away from `w₀`. -/
theorem logBall_eq_l1Ball : logBall K = l1Ball {w : InfinitePlace K // w ≠ w₀} := (rfl)

/-- The logarithmic ball is convex. -/
theorem convex_logBall : Convex ℝ (logBall K) := by
  classical
  rw [logBall_eq_l1Ball]
  exact convex_l1Ball _

/-- The logarithmic ball is symmetric about zero. -/
theorem neg_mem_logBall (x : logSpace K) : -x ∈ logBall K ↔ x ∈ logBall K := by
  classical
  rw [logBall_eq_l1Ball]
  exact neg_mem_l1Ball _ x

/-- The logarithmic ball is compact, also when the unit rank is zero. -/
theorem isCompact_logBall : IsCompact (logBall K) := by
  classical
  rw [logBall_eq_l1Ball]
  exact isCompact_l1Ball _

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
  rw [logBall_eq_l1Ball]
  exact zero_mem_interior_l1Ball _

/-- The logarithmic ball absorbs every vector in the logarithmic space. -/
theorem absorbent_logBall : Absorbent ℝ (logBall K) :=
  absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp (zero_mem_interior_logBall K))

open Classical in
/-- The gauge of the logarithmic ball is the ℓ¹ norm, rather than the ambient supremum norm. -/
theorem gauge_logBall (x : logSpace K) : gauge (logBall K) x = ∑ w, |x w| := by
  rw [logBall_eq_l1Ball]
  exact gauge_l1Ball _ x

open Classical in
/-- The logarithmic ball has volume `2 ^ r / r!` in unit rank `r`. In rank zero its volume is
one, the volume of the whole zero-dimensional logarithmic space. -/
theorem volume_logBall :
    volume (logBall K) = ENNReal.ofReal ((2 : ℝ) ^ rank K / (rank K).factorial) := by
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = rank K := by
    rw [← Module.finrank_fintype_fun_eq_card (R := ℝ),
      NumberField.Units.finrank_eq_rank]
  rw [logBall_eq_l1Ball, volume_l1Ball, hcard]

end TauCeti.NumberField.Units
