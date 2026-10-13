/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Proper

/-!
# Proper analytic maps from fan subdivisions

A subdivision of finite fans induces a toric map in the direction from the subdividing fan to
the original fan. When both fans are regular, the corresponding analytic map is proper. Indeed,
the real-linear map is the identity and each cone of the original fan is covered by the cones of
the subdivision which it contains, so the cone-by-cone properness criterion applies.

In particular, regular star subdivisions satisfying `Fan.IsSubdivision` induce proper analytic
maps.

## Main declaration

* `TauCeti.Toric.Fan.IsSubdivision.isProperMap_analyticMap`: the analytic map induced by a
  subdivision of regular fans is proper.

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
