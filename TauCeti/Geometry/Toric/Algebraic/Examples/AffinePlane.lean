/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.AffineRay
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic

/-!
# The standard affine-plane fan

The product of the two positive rank-one ray fans is the standard fan of the affine plane.
Its support is the product of the positive rays, and product regularity supplies the smooth
toric structure used by its algebraic and analytic realizations.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

namespace TauCeti.Toric

/-- The standard affine-plane fan in the product of two rank-one lattices. -/
abbrev affinePlaneFan := affineRayFan.prod affineRayFan

/-- The cones of the affine-plane fan are products of faces of the positive ray. -/
theorem mem_affinePlaneFan_cones {ξ : PointedCone ℝ ((Fin 1 → ℝ) × (Fin 1 → ℝ))} :
    ξ ∈ affinePlaneFan.cones ↔
      ∃ (σ τ : PointedCone ℝ (Fin 1 → ℝ)), σ.IsFaceOf affineRayCone ∧
        τ.IsFaceOf affineRayCone ∧ ξ = σ.prod τ := by
  simp only [affinePlaneFan, Fan.mem_prod_cones, mem_affineRayFan_cones]
  aesop

/-- The support of the affine-plane fan is the positive quadrant, expressed as a product of
the two positive rays. -/
theorem support_affinePlaneFan :
    affinePlaneFan.support = (affineRayCone : Set (Fin 1 → ℝ)) ×ˢ affineRayCone := by
  simp only [affinePlaneFan, Fan.support_prod, support_affineRayFan]

/-- The standard affine-plane fan is regular. -/
theorem isRegular_affinePlaneFan : affinePlaneFan.IsRegular :=
  Fan.IsRegular.prod affineRayFan affineRayFan isRegular_affineRayFan isRegular_affineRayFan

end TauCeti.Toric
