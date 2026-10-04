/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Divergence
public import TauCeti.Topology.JordanCurve.OnePoint

/-!
# Simple Schwarz--Christoffel boundaries through infinity

When the finite prevertices are integrable and the total exponent is at least `-1`, the
Schwarz--Christoffel boundary is proper: both ends escape every bounded subset of the plane.
If this boundary is also injective, adding the point at infinity makes it a Jordan curve in
`OnePoint ℂ`, the Riemann sphere.

This file covers total exponent at least `-1`, with the curve passing through infinity.
For total exponent less than `-1`,
`TauCeti.isJordanCurve_range_schwarzChristoffelCompactifiedBoundary` in
`SchwarzChristoffel/Compactification.lean` gives a Jordan curve in `ℂ`.

The conclusion has the Jordan-curve hypothesis shape used by
`TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_insert_infty`.
To apply that theorem to a domain `U`, one still needs to identify
`frontier U = range (schwarzChristoffelBoundary a e z₀)` and verify its other domain hypotheses.
The conclusion concerns only the boundary parametrization; it does not assert that the primitive
is univalent or that its image avoids the boundary.

For monotone prevertex data indexed by `Fin (n + 2)`, injectivity can be checked using
`TauCeti.schwarzChristoffelBoundary_injective_of_edge_intersections`.
For a general index type, injectivity must be supplied directly.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Set UpperHalfPlane

namespace TauCeti

/-- A simple proper Schwarz--Christoffel boundary, with its two ends joined at infinity, is a
Jordan curve of the Riemann sphere. Repeated prevertices are allowed, provided the sum of their
exponents is integrable. -/
theorem isJordanCurve_insert_infty_range_schwarzChristoffelBoundary
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : -1 ≤ ∑ i, e i)
    (hinj : Function.Injective (schwarzChristoffelBoundary a e z₀)) :
    IsJordanCurve (insert OnePoint.infty
      (((↑) : ℂ → OnePoint ℂ) '' range (schwarzChristoffelBoundary a e z₀))) :=
  isJordanCurve_insert_infty_range_of_isProperMap
    (isProperMap_schwarzChristoffelBoundary a e z₀ hfinite hsum) hinj

end TauCeti
