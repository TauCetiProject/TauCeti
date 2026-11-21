/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.PathConnected

/-!
# The exterior of a closed ball is path-connected

In a real normed space of dimension at least two the complement of a closed ball is path-connected:
it is the image of the product of the unit sphere with the ray `(r, ∞)` of radii exceeding the
ball's under the polar-coordinate map `(u, t) ↦ x + t • u`.

Every unbounded complementary component of a bounded set meets the exterior of any closed ball
containing that set. Connectedness of the exterior therefore forces all such components to
coincide. This uniqueness result and the corresponding filled-hull alternative are proved in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

## Main results

* `TauCeti.isPathConnected_compl_closedBall` — the exterior of a closed ball is path-connected in
  a real normed space of dimension at least two.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The exterior of a closed ball is path-connected** in a real normed space of dimension at
least two. -/
theorem isPathConnected_compl_closedBall (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPathConnected (closedBall x r)ᶜ := by
  rcases lt_or_ge r 0 with hr | hr
  · simpa [closedBall_eq_empty.mpr hr] using isPathConnected_univ
  have hIoi : IsPathConnected (Ioi r) := (convex_Ioi r).isPathConnected nonempty_Ioi
  convert ((isPathConnected_sphere h 0 zero_le_one).prod hIoi).image
    (f := fun p : E × ℝ => x + p.2 • p.1) (by fun_prop)
  ext w
  simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le, mem_image, mem_prod,
    mem_sphere_zero_iff_norm, mem_Ioi, Prod.exists]
  refine ⟨fun hw => ?_, ?_⟩
  · have hw' : w - x ≠ 0 := norm_pos_iff.mp (hr.trans_lt hw)
    exact ⟨‖w - x‖⁻¹ • (w - x), ‖w - x‖, ⟨by simp [norm_smul, hw'], hw⟩,
      by simp [smul_smul, hw']⟩
  · rintro ⟨u, t, ⟨hu, ht⟩, rfl⟩
    simpa [norm_smul, hu, abs_of_nonneg (hr.trans ht.le)] using ht

end TauCeti
