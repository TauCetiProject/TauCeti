/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Lifting changes of special-fibre coordinates

Suppose a commutative formal group law over `R` reduces to a law which a specified coordinate `ψ`
identifies with `G` over `S`. If `R → S` is surjective on coefficients and units, changing
coordinates over `R` produces an isomorphic law reducing exactly to `G`. The isomorphism
reduces to the prescribed `ψ`, not just to some isomorphism with the same target.

This lets one replace a coordinate-marked deformation by a representative whose special
fibre is fixed by equality. It does not assert that an isomorphism between reductions lifts
to an isomorphism between two previously fixed lifts: the target lift is allowed to change.
For local coefficient maps, no completeness or height hypothesis is needed.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups* (1966).
-/

public section

namespace FormalGroup

open TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A specified change of coordinates of the reduction lifts after replacing the target by
an isomorphic lift. Both series of the lifted isomorphism reduce to the prescribed coordinate
and its inverse. -/
theorem exists_iso_lifting_coordinate (F : FormalGroup R) [F.IsComm] (f : R →+* S)
    (hf : Function.Surjective f) (hu : Function.Surjective (Units.map f.toMonoidHom))
    (G : FormalGroup S) (ψ : FormalCoordinate S) (hψ : ψ • F.map f = G) :
    ∃ (H : {H : FormalGroup R // H.IsComm}) (e : FormalGroupIso F H.1),
      H.1.map f = G ∧
      PowerSeries.map f e.toHom.toPowerSeries = ψ.toPowerSeries ∧
      PowerSeries.map f e.invHom.toPowerSeries = ψ⁻¹.toPowerSeries := by
  obtain ⟨φ, hφ⟩ := (FormalCoordinate.map_surjective_iff f).2 ⟨hf, hu⟩ ψ
  refine ⟨⟨φ • F, inferInstance⟩, smulIso φ F, ?_, ?_, ?_⟩
  · rw [map_smul, hφ, hψ]
  · rw [smulIso_toHom_toPowerSeries, ← FormalCoordinate.toPowerSeries_map, hφ]
  · rw [smulIso_invHom_toPowerSeries, ← FormalCoordinate.toPowerSeries_map, map_inv, hφ]

end FormalGroup
