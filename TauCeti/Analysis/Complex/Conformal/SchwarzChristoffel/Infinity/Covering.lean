/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Covering
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.Covering

/-!
# The Schwarz--Christoffel primitive onto an unbounded polygon

Let `F = schwarzChristoffelPrimitive a e z₀` and `B = schwarzChristoffelBoundary a e z₀`. When
every finite prevertex is integrable and the total exponent `∑ i, e i` is at least `-1`, the
point at infinity of the upper half-plane is sent to infinity: `B` escapes every bounded set at
both ends of the real axis, and `F` escapes every bounded set uniformly in the upper half-plane.
The candidate polygon is then unbounded, and its boundary is the range of `B`, which is closed
because `B` is proper.

This file identifies the finite-plane closure and frontier of the image in this regime.
For compact preimages, covering maps, image equality, and bijectivity, use the more general
criteria in `TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.Covering`.

## Main results

* `TauCeti.closure_image_schwarzChristoffelPrimitive_of_neg_one_le_sum` -- the closure of the
  image is the image together with the boundary values.
* `TauCeti.frontier_image_schwarzChristoffelPrimitive_of_neg_one_le_sum` -- its frontier is the
  set of boundary values outside the image.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The closure of the image of the Schwarz--Christoffel primitive** is the image together with
the boundary values, when every finite prevertex is integrable and the total exponent is at least
`-1`. -/
theorem closure_image_schwarzChristoffelPrimitive_of_neg_one_le_sum (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hsum : -1 ≤ ∑ i, e i) :
    closure (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ∪
        range (schwarzChristoffelBoundary a e z₀) := by
  rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image,
    closure_coe_image_schwarzChristoffelPrimitive a e z₀ (fun j => (hfinite j).le),
    preimage_union, preimage_image_eq _ OnePoint.coe_injective,
    preimage_range_schwarzChristoffelSphereBoundary_of_neg_one_le_sum a e z₀ hfinite hsum]

/-- **The frontier of the image of the Schwarz--Christoffel primitive** is the set of boundary
values that the image does not cover, when every finite prevertex is integrable and the total
exponent is at least `-1`. -/
theorem frontier_image_schwarzChristoffelPrimitive_of_neg_one_le_sum (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hsum : -1 ≤ ∑ i, e i) :
    frontier (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      range (schwarzChristoffelBoundary a e z₀) \
        schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet := by
  have hopen :=
    isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl
  rw [frontier, closure_image_schwarzChristoffelPrimitive_of_neg_one_le_sum a e z₀ hfinite hsum,
    hopen.interior_eq, union_sdiff_left]

end TauCeti
