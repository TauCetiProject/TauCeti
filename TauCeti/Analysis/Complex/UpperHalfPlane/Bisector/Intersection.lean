/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Geometry
import Mathlib.Geometry.Euclidean.Basic

/-!
# Intersections of perpendicular bisectors

Two perpendicular bisectors with the same first centre and distinct second centres meet in at
most one point. This prevents distinct equality faces of a hyperbolic Dirichlet domain from
sharing a segment. No discreteness or group action is required for the geometric result.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.
-/

public section

open UpperHalfPlane Set
namespace TauCeti.UpperHalfPlane

/-- Two distinct observation points cannot be equidistant from three distinct points of the
upper half-plane. Equivalently, bisectors with a common centre and distinct other centres have
at most one common point. -/
theorem eq_of_dist_eq_dist_of_dist_eq_dist {p q r z w : ℍ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hzw : z ≠ w)
    (hzq : dist z p = dist z q) (hwq : dist w p = dist w q)
    (hzr : dist z p = dist z r) (hwr : dist w p = dist w r) : q = r := by
  -- The geometric bridge uses Mathlib's `UpperHalfPlane.dist_eq_iff_dist_coe_center_eq` and
  -- `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`.
  have hcosh (v : ℍ) : v.im * Real.cosh (dist p v) =
      ((p.re - v.re) ^ 2 + p.im ^ 2 + v.im ^ 2) / (2 * p.im) := by
    rw [cosh_dist']
    field_simp [p.im_ne_zero, v.im_ne_zero]
  have hc : (z.center (dist p z) : ℂ) ≠ (w.center (dist p w) : ℂ) := by
    intro heq
    have hre : z.re = w.re := by
      simpa only [coe_re, center_re] using
        (Complex.ext_iff.mp heq).1
    have him : z.im * Real.cosh (dist p z) = w.im * Real.cosh (dist p w) := by
      simpa only [coe_im, center_im] using (Complex.ext_iff.mp heq).2
    rw [hcosh, hcosh, hre, div_left_inj' (by positivity : (2 * p.im) ≠ 0)] at him
    have hsq : z.im ^ 2 = w.im ^ 2 := by linarith
    exact hzw (UpperHalfPlane.ext (Complex.ext hre
      ((sq_eq_sq₀ z.im_pos.le w.im_pos.le).mp hsq)))
  have h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (V := ℂ) (p := (r : ℂ)) Complex.finrank_real_complex hc
    (UpperHalfPlane.coe_injective.ne hpq)
    (dist_eq_iff_dist_coe_center_eq.mp rfl)
    (dist_eq_iff_dist_coe_center_eq.mp (by simpa only [dist_comm] using hzq.symm))
    (dist_eq_iff_dist_coe_center_eq.mp (by simpa only [dist_comm] using hzr.symm))
    (dist_eq_iff_dist_coe_center_eq.mp rfl)
    (dist_eq_iff_dist_coe_center_eq.mp (by simpa only [dist_comm] using hwq.symm))
    (dist_eq_iff_dist_coe_center_eq.mp (by simpa only [dist_comm] using hwr.symm))
  exact (UpperHalfPlane.coe_injective (h.resolve_left
    (UpperHalfPlane.coe_injective.ne hpr.symm))).symm

/-- Distinct bisectors sharing their first centre intersect in at most one point. -/
theorem subsingleton_inter_range_geodesicLine_perpBisector {p q r : ℍ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (range (geodesicLine (perpBisector p q)) ∩
      range (geodesicLine (perpBisector p r))).Subsingleton := by
  intro z hz w hw
  by_contra hzw
  exact hqr (eq_of_dist_eq_dist_of_dist_eq_dist hpq hpr hzw
    ((mem_range_geodesicLine_perpBisector_iff hpq z).mp hz.1)
    ((mem_range_geodesicLine_perpBisector_iff hpq w).mp hw.1)
    ((mem_range_geodesicLine_perpBisector_iff hpr z).mp hz.2)
    ((mem_range_geodesicLine_perpBisector_iff hpr w).mp hw.2))

end TauCeti.UpperHalfPlane
