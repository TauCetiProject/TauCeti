/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.StarSubdivision
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Proper

/-!
# Proper analytic maps from fan subdivisions

A subdivision of finite fans induces a toric map in the direction from the subdividing fan to
the original fan. When both fans are regular, the corresponding analytic map is proper. Indeed,
the real-linear map is the identity and each cone of the original fan is covered by the cones of
the subdivision which it contains, so the cone-by-cone properness criterion applies.

In particular, the star subdivision of a regular cone along a nonempty set of its rays induces a
proper analytic map to the realization of the fan of faces of the cone, the blow-down map, and so
does the star subdivision of a regular fan along a nonzero cone of the fan. The preimage of the
orbit closure of that cone under the blow-down map, the exceptional divisor, is the boundary
component of the ray through the sum of the primitive generators of its rays.

## Main declarations

* `TauCeti.Toric.Fan.IsSubdivision.isProperMap_analyticMap`: the analytic map induced by a
  subdivision of regular fans is proper.
* `TauCeti.Toric.Fan.isProperMap_analyticMap_starSubdivision`: the analytic map induced by a star
  subdivision of a regular cone is proper.
* `TauCeti.Toric.Fan.isProperMap_analyticMap_starSubdivisionAlong`: the analytic map induced by the
  star subdivision of a regular fan along a nonzero cone is proper.
* `TauCeti.Toric.Fan.preimage_analyticMap_closure_analyticConeOrbit_starSubdivisionAlong`: its
  exceptional divisor is a boundary component.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Theorem 3.4.11.
-/

public section

open Set

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ Ψ : Fan i}

/-- The analytic toric map induced by a subdivision of regular fans is proper. No nonemptiness
hypothesis is needed: for empty fans the properness conclusion follows from the sufficient half
of the cone-by-cone criterion. -/
theorem isProperMap_analyticMap (h : Φ.IsSubdivision Ψ) (hΦ : Φ.IsRegular)
    (hΨ : Ψ.IsRegular) : IsProperMap (h.toFanHom.analyticMap hΦ hΨ) := by
  apply h.toFanHom.isProperMap_analyticMap_of_preimage_realMap_subset hΦ hΨ
  intro τ x hx
  rw [h.toFanHom_realMap] at hx
  have hxτ : x ∈ (τ.1 : Set V) := by
    simpa only [Set.mem_preimage, LinearMap.id_coe, id_eq] using hx
  obtain ⟨σ, hσ, hστ, hxσ⟩ := h.exists_mem_cone τ.2 hxτ
  refine mem_iUnion₂.2 ⟨⟨σ, hσ⟩, ?_, hxσ⟩
  simpa only [h.toFanHom_realMap, PointedCone.map_id] using hστ

end TauCeti.Toric.Fan.IsSubdivision

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {τ : PointedCone ℝ V}

/-- The star subdivision of a regular cone `τ` along a nonempty set `A` of its rays induces a
proper analytic map to the realization of the fan of faces of `τ`, because the two fans have the
same support. -/
theorem isProperMap_analyticMap_starSubdivision (hi : IsIntegralLattice i)
    (hτ : IsRegularCone i τ) {A : Finset (ToricRay τ)} (hA : A.Nonempty) :
    IsProperMap ((starSubdivision_isSubdivision hi A hτ hA).toFanHom.analyticMap
      (isRegular_starSubdivision hi A hτ) (isRegular_ofCone hi hτ)) :=
  (starSubdivision_isSubdivision hi A hτ hA).isProperMap_analyticMap _ _

/-- The star subdivision of a regular fan `Φ` along a nonzero cone `σ` of `Φ` induces a proper
analytic map to the realization of `Φ`, because the two fans have the same support. -/
theorem isProperMap_analyticMap_starSubdivisionAlong (Φ : Fan i) (hΦ : Φ.IsRegular)
    {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) (hσ0 : σ ≠ ⊥) :
    IsProperMap ((Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.analyticMap
      (Φ.isRegular_starSubdivisionAlong hΦ hσ) hΦ) :=
  (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).isProperMap_analyticMap _ _

/-- The exceptional divisor of the blow-down map of the star subdivision of a regular fan `Φ` along
a nonzero cone `σ`: the preimage of the orbit closure of `σ` is the boundary component of the ray
through the sum of the primitive generators of the rays of `σ`. -/
theorem preimage_analyticMap_closure_analyticConeOrbit_starSubdivisionAlong (Φ : Fan i)
    (hΦ : Φ.IsRegular) {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) (hσ0 : σ ≠ ⊥) :
    (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.analyticMap
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) hΦ ⁻¹'
          closure (Φ.analyticConeOrbit hΦ ⟨σ, hσ⟩) =
      (Φ.starSubdivisionAlong hΦ hσ).analyticBoundaryComponent
        (Φ.isRegular_starSubdivisionAlong hΦ hσ) (Φ.starSubdivisionAlongRay hΦ hσ hσ0) := by
  rw [FanHom.preimage_analyticMap_closure_analyticConeOrbit, analyticBoundaryComponent_eq_iUnion]
  ext x
  simp only [mem_iUnion, mem_Ici, exists_prop, starSubdivisionAlongRay_le_iff_le_leastCone]

end TauCeti.Toric.Fan
