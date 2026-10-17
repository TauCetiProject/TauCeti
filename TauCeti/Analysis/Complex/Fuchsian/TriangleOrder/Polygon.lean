/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.TriangleOrder.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Triangle

/-!
# Hyperbolic triangle orders and convex polygons

This file relates the typed elliptic-order and cusp data for a hyperbolic triangle to convex
polygons in the upper half-plane. A typed triple is hyperbolic exactly when a convex triangle
realises its three associated angles. The zero-angle characterization of ideal vertices then
identifies the cusp entries with ideal vertices.

## Main result

* `TauCeti.TriangleOrder.isHyperbolic_iff_exists_interiorAngle_eq`: a triple of elliptic orders
  and cusps is hyperbolic exactly when some convex hyperbolic triangle has the corresponding
  angles.
-/

public section

noncomputable section

namespace TauCeti.TriangleOrder

/-- **Hyperbolic triangles with elliptic and cusp vertices.** A triple of elliptic orders and
cusps is hyperbolic exactly when some convex hyperbolic triangle has the corresponding angles:
`π / m` at a vertex of elliptic order `m`, and `0` at a cusp, which is then an ideal vertex by
`UpperHalfPlane.ConvexPolygon.interiorAngle_eq_zero_iff`. -/
theorem isHyperbolic_iff_exists_interiorAngle_eq {p q r : TriangleOrder} :
    IsHyperbolic p q r ↔ ∃ P : UpperHalfPlane.ConvexPolygon 3,
      P.interiorAngle 0 = p.angle ∧ P.interiorAngle 1 = q.angle ∧
        P.interiorAngle 2 = r.angle := by
  rw [UpperHalfPlane.ConvexPolygon.exists_interiorAngle_eq_iff, isHyperbolic_iff_angle_sum_lt_pi]
  exact ⟨fun h ↦ ⟨p.angle_nonneg, q.angle_nonneg, r.angle_nonneg, h⟩, fun h ↦ h.2.2.2⟩

end TauCeti.TriangleOrder
