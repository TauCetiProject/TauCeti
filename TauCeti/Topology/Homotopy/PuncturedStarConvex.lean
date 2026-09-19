/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homotopy.Equiv

/-!
# A punctured star-convex set retracts onto a sphere about the puncture

Let `V` be a subset of a real normed space which is star-convex about a point `p`, and let the
sphere `sphere p r` of some radius `r > 0` lie in `V`. Then `V \ {p}` deformation retracts onto
that sphere. The retraction is the radial projection `z ↦ p + (r / ‖z - p‖) • (z - p)`, and the
homotopy is the straight line from it to the identity. Every point of such a segment has the form
`p + c • (z - p)` with `c > 0` lying between `1` and `r / ‖z - p‖`, so it lies either on the
segment from `p` to `z` or on the segment from `p` to the radial projection of `z`; star-convexity
keeps both segments in `V`, and `c > 0` keeps them off `p`.

In particular the inclusion of the sphere into `V \ {p}` is a homotopy equivalence. For an open
convex subset of `ℂ` this is the reduction of the fundamental group of a punctured convex domain
to that of a circle.

Star-convexity about the puncture is essential: a punctured annulus is connected and open but is
not homotopy equivalent to a circle.

## Main declarations

* `StarConvex.sphereHomotopyEquiv`: the inclusion `sphere p r → V \ {p}` as a homotopy
  equivalence, with the radial projection as homotopy inverse
  (`StarConvex.coe_sphereHomotopyEquiv_apply`, `StarConvex.coe_sphereHomotopyEquiv_symm_apply`).

## References

The radial deformation retraction is the standard one; compare Hatcher, *Algebraic Topology*,
Chapter 0, where `ℝⁿ \ {0}` is deformation retracted onto the unit sphere by the same formula.
-/

public section

noncomputable section

open Metric Set
open scoped unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E} {p : E} {r : ℝ}

/-- A point `p + c • (z - p)` with `c > 0` below `1` or below `r / ‖z - p‖` stays in `V \ {p}`:
it lies on the segment from `p` to `z`, or on the segment from `p` to the radial projection of
`z` onto `sphere p r`. -/
private theorem add_smul_sub_mem_diff (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) {z : E} (hz : z ∈ V \ {p}) {c : ℝ} (hc₀ : 0 < c)
    (hc : c ≤ 1 ∨ c ≤ r / ‖z - p‖) : p + c • (z - p) ∈ V \ {p} := by
  have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz.2
  have hd : 0 < ‖z - p‖ := norm_pos_iff.mpr hzp
  refine ⟨?_, fun h => ?_⟩
  · rcases hc with hc | hc
    · exact hV.add_smul_sub_mem hz.1 hc₀.le hc
    · -- Rescale along the segment from `p` to the radial projection `w` of `z`.
      set w := p + (r / ‖z - p‖) • (z - p) with hw_def
      have hw : w ∈ V := hS <| by
        rw [mem_sphere, dist_eq_norm, hw_def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos hr hd), div_mul_cancel₀ _ hd.ne']
      have hmem := hV.add_smul_sub_mem hw (t := c * ‖z - p‖ / r) (by positivity)
        ((div_le_one hr).mpr ((le_div_iff₀ hd).mp hc))
      rwa [hw_def, add_sub_cancel_left, smul_smul,
        show c * ‖z - p‖ / r * (r / ‖z - p‖) = c by field_simp] at hmem
  · have h0 : c • (z - p) = 0 := by simpa using h
    exact hzp ((smul_eq_zero.mp h0).resolve_left hc₀.ne')

omit [NormedSpace ℝ E] in
/-- A sphere of positive radius about `p` inside `V` lies in `V \ {p}`. -/
private theorem sphere_subset_diff (hr : 0 < r) (hS : sphere p r ⊆ V) :
    sphere p r ⊆ V \ {p} := fun z hz =>
  ⟨hS hz, fun h => by
    rw [mem_singleton_iff] at h
    subst h
    simp [hr.ne] at hz⟩

/-- Radial projection of `V \ {p}` onto the sphere `sphere p r`. -/
private def radialProjection (hr : 0 < r) : C(↥(V \ {p}), sphere p r) where
  toFun z := ⟨p + (r / ‖(z : E) - p‖) • ((z : E) - p), by
    have hd : 0 < ‖(z : E) - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr z.2.2)
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hd), div_mul_cancel₀ _ hd.ne']⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hsub : Continuous fun z : ↥(V \ {p}) => (z : E) - p :=
      continuous_subtype_val.sub continuous_const
    exact continuous_const.add
      ((continuous_const.div hsub.norm fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2.2)).smul
        hsub)

/-- The straight-line homotopy from the radial projection to the identity of `V \ {p}`. -/
private def radialHomotopy (hV : StarConvex ℝ p V) (hr : 0 < r) (hS : sphere p r ⊆ V) :
    ((ContinuousMap.inclusion (sphere_subset_diff hr hS)).comp
      (radialProjection hr)).Homotopy (ContinuousMap.id ↥(V \ {p})) where
  toFun x := ⟨p + ((1 - (x.1 : ℝ)) * (r / ‖(x.2 : E) - p‖) + x.1) • ((x.2 : E) - p), by
    have hd : 0 < ‖(x.2 : E) - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr x.2.2.2)
    have ht₀ : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have ht₁ : (x.1 : ℝ) ≤ 1 := x.1.2.2
    refine add_smul_sub_mem_diff hV hr hS x.2.2 ?_ ?_
    · rcases eq_or_lt_of_le ht₁ with h | h
      · simp [h]
      · nlinarith [div_pos hr hd]
    · rcases le_total 1 (r / ‖(x.2 : E) - p‖) with h | h
      · exact Or.inr (by nlinarith)
      · exact Or.inl (by nlinarith)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hsub : Continuous fun x : I × ↥(V \ {p}) => (x.2 : E) - p :=
      (continuous_subtype_val.comp continuous_snd).sub continuous_const
    have ht : Continuous fun x : I × ↥(V \ {p}) => (x.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hdiv : Continuous fun x : I × ↥(V \ {p}) => r / ‖(x.2 : E) - p‖ :=
      continuous_const.div hsub.norm fun x => norm_ne_zero_iff.mpr (sub_ne_zero.mpr x.2.2.2)
    exact continuous_const.add ((((continuous_const.sub ht).mul hdiv).add ht).smul hsub)
  map_zero_left z := by
    ext
    simp [radialProjection]
  map_one_left z := by
    ext
    simp

/-- **A punctured star-convex set is homotopy equivalent to a sphere about the puncture.** If `V`
is star-convex about `p` and contains the sphere `sphere p r` with `r > 0`, then the inclusion
`sphere p r → V \ {p}` is a homotopy equivalence; its homotopy inverse is the radial projection
`z ↦ p + (r / ‖z - p‖) • (z - p)`. -/
def _root_.StarConvex.sphereHomotopyEquiv (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) : ContinuousMap.HomotopyEquiv (sphere p r) ↥(V \ {p}) where
  toFun := ContinuousMap.inclusion (sphere_subset_diff hr hS)
  invFun := radialProjection hr
  left_inv := by
    -- The radial projection fixes the sphere pointwise.
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id (sphere p r))
    ext x
    have hx : ‖(x : E) - p‖ = r := by simpa [dist_eq_norm] using x.2
    simp [radialProjection, hx, hr.ne']
  right_inv := ⟨radialHomotopy hV hr hS⟩

/-- The homotopy equivalence `StarConvex.sphereHomotopyEquiv` is the inclusion of the sphere. -/
@[simp]
theorem _root_.StarConvex.coe_sphereHomotopyEquiv_apply (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) (x : sphere p r) : (hV.sphereHomotopyEquiv hr hS x : E) = x :=
  (rfl)

/-- The homotopy inverse of `StarConvex.sphereHomotopyEquiv` is the radial projection onto the
sphere. -/
@[simp]
theorem _root_.StarConvex.coe_sphereHomotopyEquiv_symm_apply (hV : StarConvex ℝ p V)
    (hr : 0 < r) (hS : sphere p r ⊆ V) (z : ↥(V \ {p})) :
    ((hV.sphereHomotopyEquiv hr hS).symm z : E) = p + (r / ‖(z : E) - p‖) • ((z : E) - p) :=
  (rfl)

end TauCeti
