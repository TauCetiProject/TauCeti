/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The complement of a bounded star-convex set retracts onto a sphere

Let `K` be a subset of a real normed space which contains a point `p`, is star-convex about `p`,
and lies in the open ball `ball p r`. Then the complement `Kᶜ` deformation retracts onto the
sphere `sphere p r`. The retraction is the radial projection `z ↦ p + (r / ‖z - p‖) • (z - p)`,
and the homotopy is the straight line from it to the identity. Every point of such a segment has
the form `p + c • (z - p)` where `c` lies between `1` and `r / ‖z - p‖`. If `c ≥ 1`, the point
`z` lies on the segment from `p` to `p + c • (z - p)`, so star-convexity keeps the latter out of
`K`; if `c ≤ 1`, then `c ≥ r / ‖z - p‖` puts it outside `ball p r`.

In particular the complements of `K` and of `{p}` have the same homotopy type: this is the input
for comparing the relative homology groups `H(X, X ∖ K)` and `H(X, X ∖ {p})` in the local
homology of manifolds.

## Main declarations

* `StarConvex.complSphereHomotopyEquiv`: the inclusion `sphere p r → Kᶜ` as a homotopy
  equivalence, with the radial projection as homotopy inverse
  (`StarConvex.coe_complSphereHomotopyEquiv_apply`,
  `StarConvex.coe_complSphereHomotopyEquiv_symm_apply`).
* `TauCeti.complRadialProjection`: the radial projection `Kᶜ → sphere p r`, the restriction of
  `TauCeti.radialProjectionToSphere`.
* `StarConvex.complRadialHomotopy`: the straight-line deformation from the radial projection to
  the identity of `Kᶜ`.

## References

The radial deformation retraction is the standard one; compare Hatcher, *Algebraic Topology*,
Chapter 0, where `ℝⁿ ∖ {0}` is deformation retracted onto the unit sphere by the same formula.

The construction follows the companion construction for punctured star-convex sets in
`TauCeti.Topology.Homotopy.PuncturedStarConvex`, whose `StarConvex.sphereHomotopyEquiv` retracts
`V ∖ {p}` onto a sphere inside `V`; here the sphere lies outside `K` instead, and the radial
projection is the restriction of `TauCeti.radialProjectionToSphere`.
-/

public section

noncomputable section

open Metric Set unitInterval

namespace StarConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {p : E} {r : ℝ}

/-- A point `p + c • (z - p)` with `c > 0` and `z ∉ K` stays outside `K` when `c ≥ 1`, by
star-convexity of `K` about `p`, or when `c ≥ r / ‖z - p‖`, since it then lies outside
`ball p r ⊇ K`. -/
theorem add_smul_sub_mem_compl (hK : StarConvex ℝ p K) (hKr : K ⊆ ball p r) {z : E}
    (hz : z ∉ K) {c : ℝ} (hc : 1 ≤ c ∨ (r / ‖z - p‖ ≤ c ∧ z ≠ p)) : p + c • (z - p) ∉ K := by
  intro h
  rcases hc with hc | ⟨hc, hzp⟩
  · -- `z` lies on the segment from `p` to `p + c • (z - p)`.
    have hmem := hK.add_smul_sub_mem h (t := c⁻¹) (by positivity) (inv_le_one_of_one_le₀ hc)
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (by positivity), one_smul,
      add_sub_cancel] at hmem
    exact hz hmem
  · have hd : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
    have hr : r ≤ c * ‖z - p‖ := (div_le_iff₀ hd).mp hc
    have hlt := hKr h
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hlt
    exact (le_abs_self c |> (mul_le_mul_of_nonneg_right · hd.le) |> hr.trans |>
      not_lt.mpr) hlt

end StarConvex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {p : E} {r : ℝ}

/-- Radial projection of `Kᶜ` onto the sphere `sphere p r`, for `p ∈ K ⊆ ball p r`: the
restriction of `TauCeti.radialProjectionToSphere` along `Kᶜ ⊆ univ ∖ {p}`. -/
def complRadialProjection (hp : p ∈ K) (hKr : K ⊆ ball p r) : C(↥Kᶜ, sphere p r) :=
  (radialProjectionToSphere (V := univ) (by simpa using hKr hp)).comp
    (ContinuousMap.inclusion fun _ hz ↦ ⟨mem_univ _, fun h ↦ hz (mem_singleton_iff.1 h ▸ hp)⟩)

/-- The radial projection onto `sphere p r` is `z ↦ p + (r / ‖z - p‖) • (z - p)`. -/
@[simp]
theorem coe_complRadialProjection_apply (hp : p ∈ K) (hKr : K ⊆ ball p r) (z : ↥Kᶜ) :
    (complRadialProjection hp hKr z : E) = p + (r / ‖(z : E) - p‖) • ((z : E) - p) :=
  coe_radialProjectionToSphere_apply _ _

end TauCeti

namespace StarConvex

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {p : E} {r : ℝ}

omit [NormedSpace ℝ E] in
/-- The points of `Kᶜ` differ from `p` when `p ∈ K`. -/
private theorem sub_ne_zero_of_mem_compl (hp : p ∈ K) {z : E} (hz : z ∈ Kᶜ) : z - p ≠ 0 :=
  sub_ne_zero.mpr fun h ↦ hz (h ▸ hp)

/-- The straight-line homotopy from the radial projection onto `sphere p r` to the identity of
`Kᶜ`, for `K` star-convex about `p ∈ K` and contained in `ball p r`. -/
def complRadialHomotopy (hK : StarConvex ℝ p K) (hp : p ∈ K) (hKr : K ⊆ ball p r) :
    ((ContinuousMap.inclusion (sphere_disjoint_ball.mono_right hKr).subset_compl_right).comp
      (complRadialProjection hp hKr)).Homotopy (ContinuousMap.id ↥Kᶜ) where
  toFun x := ⟨p + ((1 - (x.1 : ℝ)) * (r / ‖(x.2 : E) - p‖) + x.1) • ((x.2 : E) - p), by
    have hzp : (x.2 : E) ≠ p := sub_ne_zero.mp (sub_ne_zero_of_mem_compl hp x.2.2)
    have ht₀ : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have ht₁ : (x.1 : ℝ) ≤ 1 := x.1.2.2
    refine hK.add_smul_sub_mem_compl hKr x.2.2 ?_
    rcases le_total 1 (r / ‖(x.2 : E) - p‖) with h | h
    · exact Or.inl (by nlinarith)
    · exact Or.inr ⟨by nlinarith, hzp⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hsub : Continuous fun x : I × ↥Kᶜ ↦ (x.2 : E) - p :=
      (continuous_subtype_val.comp continuous_snd).sub continuous_const
    have ht : Continuous fun x : I × ↥Kᶜ ↦ (x.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hdiv : Continuous fun x : I × ↥Kᶜ ↦ r / ‖(x.2 : E) - p‖ :=
      continuous_const.div hsub.norm fun x ↦
        norm_ne_zero_iff.mpr (sub_ne_zero_of_mem_compl hp x.2.2)
    exact continuous_const.add ((((continuous_const.sub ht).mul hdiv).add ht).smul hsub)
  map_zero_left z := by
    ext
    simp
  map_one_left z := by
    ext
    simp

/-- The radial deformation of `Kᶜ` has the stated pointwise straight-line formula. -/
@[simp]
theorem coe_complRadialHomotopy_apply (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (t : I) (z : ↥Kᶜ) :
    ((hK.complRadialHomotopy hp hKr (t, z) : ↥Kᶜ) : E) =
      p + ((1 - (t : ℝ)) * (r / ‖(z : E) - p‖) + t) • ((z : E) - p) :=
  (rfl)

/-- The radial deformation of `Kᶜ` fixes every included point of the sphere throughout the
homotopy. -/
@[simp]
theorem complRadialHomotopy_apply_inclusion (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (t : I) (x : sphere p r) :
    hK.complRadialHomotopy hp hKr
        (t, Set.inclusion (sphere_disjoint_ball.mono_right hKr).subset_compl_right x) =
      Set.inclusion (sphere_disjoint_ball.mono_right hKr).subset_compl_right x := by
  ext
  have hx : ‖(x : E) - p‖ = r := by simpa [dist_eq_norm] using x.2
  simp [hx, div_self (pos_of_mem_ball (hKr hp)).ne']

/-- **The complement of a bounded star-convex set is homotopy equivalent to a sphere.** If `K`
contains `p`, is star-convex about `p` and lies in `ball p r`, then the inclusion
`sphere p r → Kᶜ` is a homotopy equivalence; its homotopy inverse is the radial projection
`z ↦ p + (r / ‖z - p‖) • (z - p)`. -/
def complSphereHomotopyEquiv (hK : StarConvex ℝ p K) (hp : p ∈ K) (hKr : K ⊆ ball p r) :
    ContinuousMap.HomotopyEquiv (sphere p r) ↥Kᶜ where
  toFun := ContinuousMap.inclusion (sphere_disjoint_ball.mono_right hKr).subset_compl_right
  invFun := complRadialProjection hp hKr
  left_inv := by
    -- The radial projection fixes the sphere pointwise.
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id (sphere p r))
    ext x
    have hx : ‖(x : E) - p‖ = r := by simpa [dist_eq_norm] using x.2
    simp [hx, div_self (pos_of_mem_ball (hKr hp)).ne']
  right_inv := ⟨hK.complRadialHomotopy hp hKr⟩

/-- The homotopy equivalence `StarConvex.complSphereHomotopyEquiv` is the inclusion of the
sphere. -/
@[simp]
theorem coe_complSphereHomotopyEquiv_apply (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (x : sphere p r) :
    (hK.complSphereHomotopyEquiv hp hKr x : E) = x :=
  (rfl)

/-- The homotopy inverse of `StarConvex.complSphereHomotopyEquiv` is the radial projection onto
the sphere. -/
@[simp]
theorem coe_complSphereHomotopyEquiv_symm_apply (hK : StarConvex ℝ p K) (hp : p ∈ K)
    (hKr : K ⊆ ball p r) (z : ↥Kᶜ) :
    ((hK.complSphereHomotopyEquiv hp hKr).symm z : E) =
      p + (r / ‖(z : E) - p‖) • ((z : E) - p) :=
  coe_complRadialProjection_apply hp hKr z

end StarConvex
