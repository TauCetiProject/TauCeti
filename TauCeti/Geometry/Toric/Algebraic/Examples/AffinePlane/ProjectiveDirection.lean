/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.AffinePlane.Basic
public import TauCeti.Geometry.Toric.Algebraic.Examples.ProjectiveLine

/-!
# The projective-direction morphism of the plane blow-up fan

The lattice map `(a, b) ↦ b - a` sends the upper blow-up cone to the positive ray and the
lower cone to the negative ray. It therefore defines a morphism from the plane blow-up fan
to the projective-line fan. Its analytic realization records the direction `[x : y]` of a
point above the plane, including the directions above the origin.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

namespace TauCeti.Toric

/-- The morphism to the projective-line fan that records the direction in the plane blow-up.
Its lattice map is `(a, b) ↦ b - a`, annihilating the diagonal ray. -/
def affinePlaneBlowUpDirectionFanHom : FanHom affinePlaneBlowUpFan projectiveLineFan where
  latticeMap := AddMonoidHom.snd _ _ - AddMonoidHom.fst _ _
  realMap := LinearMap.snd ℝ _ _ - LinearMap.fst ℝ _ _
  map_lattice n := by ext j; simp
  map_cone σ hσ := by
    rcases mem_affinePlaneBlowUpFan_cones.1 hσ with hσ | hσ
    · refine ⟨negativeRayCone, negativeRayCone_mem_projectiveLineFan, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      simpa using (mem_affinePlaneBlowUpLowerCone_iff x).1 (hσ.le hx) |>.2
    · refine ⟨affineRayCone, affineRayCone_mem_projectiveLineFan, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      simpa using (mem_affinePlaneBlowUpUpperCone_iff x).1 (hσ.le hx) |>.2

/-- The projective-direction lattice map is the difference of the two coordinates. -/
@[simp]
theorem affinePlaneBlowUpDirectionFanHom_latticeMap (n : (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    affinePlaneBlowUpDirectionFanHom.latticeMap n = n.2 - n.1 := (rfl)

/-- The real extension of the projective-direction lattice map is the coordinate difference. -/
@[simp]
theorem affinePlaneBlowUpDirectionFanHom_realMap (x : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    affinePlaneBlowUpDirectionFanHom.realMap x = x.2 - x.1 := (rfl)

/-- The upper blow-up cone maps into the positive projective-line cone. -/
theorem mapsTo_affinePlaneBlowUpDirectionFanHom_upper :
    Set.MapsTo affinePlaneBlowUpDirectionFanHom.realMap
      (affinePlaneBlowUpUpperCone : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))) affineRayCone := by
  intro x hx
  simpa using (mem_affinePlaneBlowUpUpperCone_iff x).1 hx |>.2

/-- The lower blow-up cone maps into the negative projective-line cone. -/
theorem mapsTo_affinePlaneBlowUpDirectionFanHom_lower :
    Set.MapsTo affinePlaneBlowUpDirectionFanHom.realMap
      (affinePlaneBlowUpLowerCone : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))) negativeRayCone := by
  intro x hx
  simpa using (mem_affinePlaneBlowUpLowerCone_iff x).1 hx |>.2

end TauCeti.Toric
