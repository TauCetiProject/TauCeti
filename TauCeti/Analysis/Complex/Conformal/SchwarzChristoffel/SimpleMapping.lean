/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.BoundarySheet
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.SimpleBoundary
import TauCeti.Order.Interval.Finite

/-!
# The Schwarz--Christoffel map of a simple polygon

When its compactified boundary is a simple curve, the Schwarz--Christoffel primitive maps the
upper half-plane bijectively onto the complementary component containing its base-point image.
This identifies the image component for simple polygons, including those with reentrant corners.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A simple compactified Schwarz--Christoffel boundary makes the primitive a bijection from
the upper half-plane onto the complementary component containing its base-point image. -/
theorem bijOn_schwarzChristoffelPrimitive_of_simple_boundary
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet
      (connectedComponentIn (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀)) := by
  obtain ⟨p, q, x, ha, hx⟩ := exists_Ioo_disjoint_range_of_finite a
  have havoid : Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (schwarzChristoffelFiniteBoundary a e z₀) := by
    rw [schwarzChristoffelFiniteBoundary_eq_range_compactifiedBoundary a e z₀ hfinite hinfty]
    exact disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj
  have hunique (t : OnePoint ℝ) (ht : schwarzChristoffelSphereBoundary a e z₀ t =
      schwarzChristoffelSphereBoundary a e z₀ (x : OnePoint ℝ)) : t = (x : OnePoint ℝ) := by
    rw [schwarzChristoffelSphereBoundary_eq_coe_compactifiedBoundary
      a e z₀ hfinite hinfty] at ht
    exact hinj (OnePoint.coe_injective ht)
  rw [← schwarzChristoffelFiniteBoundary_eq_range_compactifiedBoundary a e z₀ hfinite hinfty]
  exact bijOn_schwarzChristoffelPrimitive_connectedComponentIn_of_unique_boundary_value
    a e z₀ (fun j => (hfinite j).le) havoid (fun i _ => ha i) hx hunique

end TauCeti
