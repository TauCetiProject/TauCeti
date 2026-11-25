/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.Isoperimetric
public import TauCeti.Analysis.Complex.Rectangle
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import Mathlib.Analysis.Convex.Measure

/-!
# The isoperimetric inequality for planar convex sets

Let `s ⊆ ℂ` be a bounded convex set with nonempty interior. Its frontier is a Jordan curve
(`TauCeti.isJordanCurve_frontier_of_convex`), whose filled hull is the closure of `s` and whose
inside is the interior of `s` (`Convex.filledHull_frontier` and
`Convex.filledHull_frontier_sdiff_frontier`). Since the frontier of a convex set is Lebesgue-null,
the isoperimetric inequality for Jordan curves becomes

`4π |s| ≤ H¹(frontier s)²`,

with equality exactly when the closure of `s` is a closed disc of positive radius
(`Convex.ofReal_four_pi_mul_volume_le` and `Convex.ofReal_four_pi_mul_volume_eq_iff`). Both are
stated in `ℝ≥0∞`, so no rectifiability of the frontier is assumed. The inequality needs no
interior point: a convex set with empty interior is null.

So every bounded convex set with nonempty interior whose closure is not a disc satisfies the
strict inequality (`Convex.ofReal_four_pi_mul_volume_lt_iff`). This applies to every closed
rectangle with sides of positive length, squares included
(`Complex.ofReal_four_pi_mul_volume_rectangle_lt`): a closed disc is strictly convex, while the
midpoint of an edge of a rectangle is not an interior point (`Complex.rectangle_ne_closedBall`).

## References

* R. Osserman, *The isoperimetric inequality*, Bull. Amer. Math. Soc. **84** (1978), 1182–1238.
-/

public section

open MeasureTheory Metric Set TauCeti
open scoped ENNReal Real

namespace Convex

variable {s : Set ℂ}

/-- The filled hull of the frontier of a bounded convex set `s ⊆ ℂ` with nonempty interior is
the closure of `s`. -/
theorem filledHull_frontier (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) : filledHull (frontier s) = closure s := by
  have hfr : frontier (closure s) = frontier s := by
    rw [frontier, frontier, closure_closure,
      hs.interior_closure_eq_interior_of_nonempty_interior hne]
  rw [← hfr]
  exact (hfr ▸ isJordanCurve_frontier_of_convex hs hne hb).filledHull_frontier_eq
    hb.isCompact_closure (hne.mono (interior_mono subset_closure))

/-- The inside of the frontier of a bounded convex set `s ⊆ ℂ` with nonempty interior, as a
Jordan curve, is the interior of `s`. -/
theorem filledHull_frontier_sdiff_frontier (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) : filledHull (frontier s) \ frontier s = interior s := by
  rw [hs.filledHull_frontier hne hb, closure_sdiff_frontier]

/-- The frontier of a bounded convex set `s ⊆ ℂ` with nonempty interior is a circle exactly when
the closure of `s` is the closed disc it bounds. -/
theorem frontier_eq_sphere_iff (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) {c : ℂ} {r : ℝ} :
    frontier s = sphere c r ↔ closure s = closedBall c r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases lt_or_ge r 0 with hr | hr
    · have hJ := isJordanCurve_frontier_of_convex hs hne hb
      rw [h, sphere_eq_empty_of_neg hr] at hJ
      exact (hJ.nonempty.ne_empty rfl).elim
    · rw [← hs.filledHull_frontier hne hb, h, filledHull_sphere c hr]
  · rw [← (isJordanCurve_frontier_of_convex hs hne hb).frontier_filledHull,
      hs.filledHull_frontier hne hb, h, frontier_closedBall' c r]

/-- The volume of a convex set `s ⊆ ℂ` is the area of the inside of its frontier, provided `s` is
bounded with nonempty interior. -/
private theorem volume_eq_volume_filledHull_frontier_sdiff (hs : Convex ℝ s)
    (hne : (interior s).Nonempty) (hb : Bornology.IsBounded s) :
    volume s = volume (filledHull (frontier s) \ frontier s) := by
  rw [hs.filledHull_frontier_sdiff_frontier hne hb,
    measure_interior_of_null_frontier (hs.addHaar_frontier volume)]

/-- **The isoperimetric inequality for a planar convex set.** A bounded convex set `s ⊆ ℂ`
satisfies `4π |s| ≤ H¹(frontier s)²` in `ℝ≥0∞`. No rectifiability of the frontier is assumed, and
a convex set with empty interior is null. -/
theorem ofReal_four_pi_mul_volume_le (hs : Convex ℝ s) (hb : Bornology.IsBounded s) :
    ENNReal.ofReal (4 * π) * volume s ≤ μHE[1] (frontier s) ^ 2 := by
  rcases (interior s).eq_empty_or_nonempty with hint | hne
  · -- With empty interior the closure of `s` is its frontier, which is null.
    have hnull : volume s = 0 := measure_mono_null
      (by rw [← closure_sdiff_interior, hint, sdiff_empty]; exact subset_closure)
      (hs.addHaar_frontier volume)
    simp [hnull]
  · rw [hs.volume_eq_volume_filledHull_frontier_sdiff hne hb]
    exact (isJordanCurve_frontier_of_convex hs hne hb).ofReal_four_pi_mul_volume_filledHull_sdiff_le

/-- **Equality in the isoperimetric inequality for a planar convex set.** A bounded convex set
`s ⊆ ℂ` with nonempty interior satisfies `4π |s| = H¹(frontier s)²` in `ℝ≥0∞` exactly when its
closure is a closed disc of positive radius. -/
theorem ofReal_four_pi_mul_volume_eq_iff (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) :
    ENNReal.ofReal (4 * π) * volume s = μHE[1] (frontier s) ^ 2 ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ closure s = closedBall c r := by
  rw [hs.volume_eq_volume_filledHull_frontier_sdiff hne hb,
    (isJordanCurve_frontier_of_convex hs hne hb).ofReal_four_pi_mul_volume_filledHull_sdiff_eq_iff]
  simp_rw [hs.frontier_eq_sphere_iff hne hb]

/-- **The strict isoperimetric inequality for a planar convex set.** A bounded convex set
`s ⊆ ℂ` with nonempty interior satisfies `4π |s| < H¹(frontier s)²` in `ℝ≥0∞` exactly when its
closure is not a closed disc of positive radius. -/
theorem ofReal_four_pi_mul_volume_lt_iff (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) :
    ENNReal.ofReal (4 * π) * volume s < μHE[1] (frontier s) ^ 2 ↔
      ¬∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ closure s = closedBall c r := by
  rw [← hs.ofReal_four_pi_mul_volume_eq_iff hne hb, lt_iff_le_and_ne,
    and_iff_right (hs.ofReal_four_pi_mul_volume_le hb)]

end Convex

namespace Complex

variable {z w : ℂ}

/-- **The isoperimetric inequality is strict for rectangles.** A closed rectangle `R ⊆ ℂ` with
sides of positive length satisfies `4π |R| < H¹(frontier R)²`. -/
theorem ofReal_four_pi_mul_volume_rectangle_lt (hre : z.re ≠ w.re) (him : z.im ≠ w.im) :
    ENNReal.ofReal (4 * π) * volume (Rectangle z w) < μHE[1] (frontier (Rectangle z w)) ^ 2 := by
  rw [(convex_rectangle z w).ofReal_four_pi_mul_volume_lt_iff
    (interior_rectangle_nonempty hre him) (isCompact_rectangle z w).isBounded,
    (isClosed_rectangle z w).closure_eq]
  rintro ⟨c, r, -, h⟩
  exact rectangle_ne_closedBall (fun h ↦ hre (congrArg re h)) c r h

end Complex
