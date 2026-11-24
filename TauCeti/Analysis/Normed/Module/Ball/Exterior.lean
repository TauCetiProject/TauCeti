/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# The exterior of a closed ball is path-connected

In a real normed space of dimension at least two the complement of a closed ball is path-connected:
it is the image of the product of the unit sphere with the ray `(r, ∞)` of radii exceeding the
ball's under the polar-coordinate map `(u, t) ↦ x + t • u`.

Every unbounded complementary component of a bounded set meets the exterior of any closed ball
containing that set. Connectedness of the exterior therefore forces all such components to
coincide. This uniqueness result and the corresponding filled-hull alternative are proved in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

The file also records how nonzero scalar dilation acts on the complement of a closed ball
(`TauCeti.smul_compl_closedBall`) and bounds the norm along an outward radial segment
(`TauCeti.norm_mem_segment_smul_bounds`).

## Main results

* `TauCeti.isPathConnected_compl_closedBall` — the exterior of a closed ball is path-connected in
  a real normed space of dimension at least two.
* `TauCeti.smul_compl_closedBall` — nonzero scalar multiplication maps `(closedBall x r)ᶜ` onto
  `(closedBall (c • x) (‖c‖ * r))ᶜ`.
* `TauCeti.norm_mem_segment_smul_bounds` — every point on the segment from `x` to `c • x`
  (`1 ≤ c`) satisfies `‖x‖ ≤ ‖z‖ ≤ c * ‖x‖`.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set
open scoped Pointwise

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

/-- Scaling by a nonzero scalar `c` maps the exterior of `closedBall x r` onto the exterior of
`closedBall (c • x) (‖c‖ * r)`. -/
theorem smul_compl_closedBall {𝕜 F : Type*} [NormedField 𝕜] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {c : 𝕜} (hc : c ≠ 0) (x : F) (r : ℝ) :
    c • (closedBall x r)ᶜ = (closedBall (c • x) (‖c‖ * r))ᶜ := by
  rw [← Set.image_smul, Set.image_compl_eq (IsUnit.mk0 c hc).smul_bijective,
    Set.image_smul, smul_closedBall' hc]

/-- Every point `z` on the segment from `x` to `c • x` with `1 ≤ c` satisfies `‖x‖ ≤ ‖z‖` and
`‖z‖ ≤ c * ‖x‖`. -/
theorem norm_mem_segment_smul_bounds {c : ℝ} (hc : 1 ≤ c) {x z : E}
    (hz : z ∈ segment ℝ x (c • x)) :
    ‖x‖ ≤ ‖z‖ ∧ ‖z‖ ≤ c * ‖x‖ := by
  rw [segment_eq_image] at hz
  obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := hz
  have h1 : 1 ≤ (1 - τ) + τ * c := by nlinarith
  have h2 : (1 - τ) + τ * c ≤ c := by nlinarith
  have hcomb : (1 - τ) • x + τ • (c • x) = ((1 - τ) + τ * c) • x := by
    rw [smul_smul, ← add_smul]
  dsimp only
  rw [hcomb, norm_smul, Real.norm_of_nonneg (zero_le_one.trans h1)]
  exact ⟨le_mul_of_one_le_left (norm_nonneg x) h1, mul_le_mul_of_nonneg_right h2 (norm_nonneg x)⟩

end TauCeti
