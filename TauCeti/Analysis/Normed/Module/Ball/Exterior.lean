/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Path-connected exteriors of closed balls and of unions of bounded closed convex sets

In a real normed space of dimension at least two the complement of a closed ball is path-connected:
it is the image of the product of the unit sphere with the ray `(r, ∞)` of radii exceeding the
ball's under the polar-coordinate map `(u, t) ↦ x + t • u`. By Hahn–Banach separation, every point
outside the union of two bounded closed convex sets can be pushed along a ray staying in two
closed half-spaces avoiding both sets into the exterior of a larger ball containing them, so the
complement of their union (and in particular of the union of two closed balls) is also
path-connected.

Every unbounded complementary component of a bounded set meets the exterior of any closed ball
containing that set. Connectedness of the exterior therefore forces all such components to
coincide. This uniqueness result and the corresponding filled-hull alternative are proved in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

## Main results

* `TauCeti.isPathConnected_compl_closedBall` — the exterior of a closed ball is path-connected in
  a real normed space of dimension at least two.
* `TauCeti.isPathConnected_compl_union_of_convex_of_isClosed_of_isBounded` — the exterior of a
  union of two bounded closed convex sets is path-connected in a real normed space of dimension at
  least two.
* `TauCeti.isPathConnected_compl_union_closedBall` — the exterior of a union of two closed balls
  is path-connected in a real normed space of dimension at least two.

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

/-- **The exterior of a union of two bounded closed convex sets is path-connected** in a real
normed space of dimension at least two. -/
theorem isPathConnected_compl_union_of_convex_of_isClosed_of_isBounded
    (h : 1 < Module.rank ℝ E) {s t : Set E} (hs : Convex ℝ s) (hs_closed : IsClosed s)
    (hs_bdd : Bornology.IsBounded s) (ht : Convex ℝ t) (ht_closed : IsClosed t)
    (ht_bdd : Bornology.IsBounded t) :
    IsPathConnected (s ∪ t)ᶜ := by
  have : Nontrivial E := rank_pos_iff_nontrivial.mp (zero_lt_one.trans h)
  let U : Set E := (s ∪ t)ᶜ
  obtain ⟨R₁, hs₁⟩ := hs_bdd.subset_closedBall (0 : E)
  obtain ⟨R₂, ht₁⟩ := ht_bdd.subset_closedBall (0 : E)
  let R : ℝ := max 0 (max R₁ R₂)
  have hRU : (closedBall (0 : E) R)ᶜ ⊆ U := by
    refine compl_subset_compl.mpr (union_subset ?_ ?_)
    · exact hs₁.trans (closedBall_subset_closedBall ((le_max_left R₁ R₂).trans (le_max_right 0 _)))
    · exact ht₁.trans (closedBall_subset_closedBall ((le_max_right R₁ R₂).trans (le_max_right 0 _)))
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : E)
  let p₀ : E := ((R + 1) / ‖u₀‖) • u₀
  have hp₀R : p₀ ∈ (closedBall (0 : E) R)ᶜ := by
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le, norm_smul,
      Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hu₀)]
    linarith
  refine ⟨p₀, hRU hp₀R, fun z hz => ?_⟩
  rw [mem_compl_iff, mem_union, not_or] at hz
  obtain ⟨f₁, c₁, hfz₁, hfc₁⟩ := geometric_hahn_banach_point_closed hs hs_closed hz.1
  obtain ⟨f₂, c₂, hfz₂, hfc₂⟩ := geometric_hahn_banach_point_closed ht ht_closed hz.2
  obtain ⟨v, hv_ne, hv_f₁, hv_f₂⟩ :=
    Module.Dual.exists_ne_zero_apply_nonpos h f₁.toLinearMap f₂.toLinearMap
  obtain ⟨T, hT_pos, hzT_R⟩ :=
    exists_pos_add_smul_notMem_closedBall z 0 (norm_ne_zero_iff.mpr hv_ne) R
  have hjoin_ray : JoinedIn U z (z + T • v) := by
    refine JoinedIn.of_segment_subset ?_
    rw [segment_eq_image_lineMap]
    rintro _ ⟨τ, hτ, rfl⟩
    have hτ0 : 0 ≤ τ * T := mul_nonneg hτ.1 hT_pos.le
    have hline : AffineMap.lineMap z (z + T • v) τ = z + (τ * T) • v := by
      simp only [AffineMap.lineMap_apply_module]
      module
    rw [hline, mem_compl_iff, mem_union, not_or]
    exact ⟨add_smul_notMem_of_linearMap_lt (fun y hy => hfz₁.trans (hfc₁ y hy)) hv_f₁ hτ0,
      add_smul_notMem_of_linearMap_lt (fun y hy => hfz₂.trans (hfc₂ y hy)) hv_f₂ hτ0⟩
  exact ((hjoin_ray.trans ((isPathConnected_compl_closedBall h 0 R).joinedIn
    (z + T • v) hzT_R p₀ hp₀R |>.mono hRU)).symm)

/-- **The exterior of a union of two closed balls is path-connected** in a real normed space of
dimension at least two. -/
theorem isPathConnected_compl_union_closedBall (h : 1 < Module.rank ℝ E) (x₁ x₂ : E) (r₁ r₂ : ℝ) :
    IsPathConnected (closedBall x₁ r₁ ∪ closedBall x₂ r₂)ᶜ :=
  isPathConnected_compl_union_of_convex_of_isClosed_of_isBounded h
    (convex_closedBall x₁ r₁) isClosed_closedBall isBounded_closedBall
    (convex_closedBall x₂ r₂) isClosed_closedBall isBounded_closedBall

end TauCeti
