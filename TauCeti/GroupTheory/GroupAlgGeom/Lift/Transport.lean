/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.ChangeOfCoordinates
public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic

/-!
# Lifts under changes of coordinates

A change of coordinates, a bijective `G`-homomorphism `σ : G[X'] → G[X]`, transforms a system
`S ⊆ G[X]` into `σ ⁻¹' S ⊆ G[X']` and, extended by the identity on further variables `Y`
(`TauCeti.GroupAlgGeom.sumExtend`), a system `T ⊆ G[X ⊔ Y]` into `sumExtend Y σ ⁻¹' T` in
`G[X' ⊔ Y]`. Compatibility, lifts and complete lifts are invariant under this transformation, and
the solutions at the generic points correspond under the induced isomorphism of coordinate groups
`G_{R(σ⁻¹S)} ≃ G_{R(S)}` (`TauCeti.GroupAlgGeom.CoordGroup.equivOfCoordinateChange`). A family of
solutions of `S` is generic exactly when its image under the word map of `σ` is generic for
`σ ⁻¹' S`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.isCompatible_preimage_iff`,
  `TauCeti.GroupAlgGeom.Lift.isCompatibleNe_preimage_iff`: invariance of compatibility.
* `TauCeti.GroupAlgGeom.Lift.sumElim_genericPoint_mem_V_preimage_iff`: the formal solutions
  correspond under the induced isomorphism of coordinate groups.
* `TauCeti.GroupAlgGeom.Lift.hasLift_preimage_iff`,
  `TauCeti.GroupAlgGeom.Lift.hasLiftNe_preimage_iff`,
  `TauCeti.GroupAlgGeom.Lift.hasCompleteLift_preimage_iff`: invariance of lifts and complete
  lifts.
* `TauCeti.GroupAlgGeom.Lift.isGenericFamily_preimage_image_iff`: invariance of generic families.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §6, Definitions 24–27.
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

open Monoid.Coprod

variable {G H X X' Y : Type*} [Group G] [Group H]
  {σ : GHom (inl : G →* GX G X') (inl : G →* GX G X)} (hσ : Function.Bijective σ)
  {ι : G →* H} {S : Set (GX G X)} {T : Set (GX G (X ⊕ Y))}

include hσ

/-- Compatibility is invariant under a change of coordinates. -/
theorem isCompatible_preimage_iff : IsCompatible ι (σ ⁻¹' S) (sumExtend Y σ ⁻¹' T) ↔
    IsCompatible ι S T := by
  rw [isCompatible_iff, isCompatible_iff, (coordinateChangeEquiv ι σ hσ).surjective.forall]
  simp [wordMap_mem_V_iff ι σ hσ.2, sumElim_wordMap_mem_V_preimage_iff ι hσ.2]

/-- Compatibility of a system with an inequation is invariant under a change of coordinates. -/
theorem isCompatibleNe_preimage_iff {W : GX G (X' ⊕ Y)} :
    IsCompatibleNe ι (σ ⁻¹' S) (sumExtend Y σ ⁻¹' T) W ↔
      IsCompatibleNe ι S T (sumExtend Y σ W) := by
  rw [isCompatibleNe_iff, isCompatibleNe_iff,
    (coordinateChangeEquiv ι σ hσ).surjective.forall]
  simp [wordMap_mem_V_iff ι σ hσ.2, sumElim_wordMap_mem_V_preimage_iff ι hσ.2]

/-- The isomorphism of coordinate groups induced by a change of coordinates carries the value of
a word at a point over the generic point of the transformed system to the value of its image
under `sumExtend Y σ` at the corresponding point over the generic point of the system. -/
theorem eval_sumElim_genericPoint_sumExtend (w : Y → CoordGroup ι (σ ⁻¹' S)) (u : GX G (X' ⊕ Y)) :
    eval (CoordGroup.coeff ι S)
        (Sum.elim (CoordGroup.genericPoint ι S) (CoordGroup.equivOfCoordinateChange ι σ hσ S ∘ w))
        (sumExtend Y σ u) =
      CoordGroup.equivOfCoordinateChange ι σ hσ S
        (eval (CoordGroup.coeff ι (σ ⁻¹' S)) (Sum.elim (CoordGroup.genericPoint ι (σ ⁻¹' S)) w)
          u) := by
  have he : (CoordGroup.equivOfCoordinateChange ι σ hσ S :
      CoordGroup ι (σ ⁻¹' S) →* CoordGroup ι S).comp (CoordGroup.coeff ι (σ ⁻¹' S)) =
      CoordGroup.coeff ι S :=
    MonoidHom.ext (CoordGroup.equivOfCoordinateChange_coeff ι σ hσ S)
  rw [hom_eval, he, Sum.comp_elim, CoordGroup.equivOfCoordinateChange_comp_genericPoint,
    eval_sumExtend]

/-- Under a change of coordinates, the solutions of the transformed system `sumExtend Y σ ⁻¹' T`
over the generic point of `σ ⁻¹' S` correspond to the solutions of `T` over the generic point of
`S`, under the induced isomorphism of coordinate groups. -/
theorem sumElim_genericPoint_mem_V_preimage_iff {w : Y → CoordGroup ι (σ ⁻¹' S)} :
    Sum.elim (CoordGroup.genericPoint ι (σ ⁻¹' S)) w ∈
        V (CoordGroup.coeff ι (σ ⁻¹' S)) (sumExtend Y σ ⁻¹' T) ↔
      Sum.elim (CoordGroup.genericPoint ι S) (CoordGroup.equivOfCoordinateChange ι σ hσ S ∘ w) ∈
        V (CoordGroup.coeff ι S) T := by
  simp only [mem_V, Set.mem_preimage]
  rw [(sumExtend_surjective (Y := Y) hσ.2).forall]
  refine forall₂_congr fun u _ => ?_
  rw [eval_sumElim_genericPoint_sumExtend,
    map_eq_one_iff _ (CoordGroup.equivOfCoordinateChange ι σ hσ S).injective]

/-- The existence of a lift is invariant under a change of coordinates. -/
theorem hasLift_preimage_iff : HasLift ι (σ ⁻¹' S) (sumExtend Y σ ⁻¹' T) ↔ HasLift ι S T := by
  rw [hasLift_iff, hasLift_iff,
    (CoordGroup.equivOfCoordinateChange ι σ hσ S).surjective.comp_left.exists]
  exact exists_congr fun w => sumElim_genericPoint_mem_V_preimage_iff hσ

/-- The existence of a lift of a system with an inequation is invariant under a change of
coordinates. -/
theorem hasLiftNe_preimage_iff {W : GX G (X' ⊕ Y)} :
    HasLiftNe ι (σ ⁻¹' S) (sumExtend Y σ ⁻¹' T) W ↔ HasLiftNe ι S T (sumExtend Y σ W) := by
  rw [hasLiftNe_iff, hasLiftNe_iff,
    (CoordGroup.equivOfCoordinateChange ι σ hσ S).surjective.comp_left.exists]
  refine exists_congr fun w => and_congr (sumElim_genericPoint_mem_V_preimage_iff hσ) ?_
  rw [eval_sumElim_genericPoint_sumExtend hσ,
    map_ne_one_iff _ (CoordGroup.equivOfCoordinateChange ι σ hσ S).injective]

/-- The existence of a complete lift is invariant under a change of coordinates. -/
theorem hasCompleteLift_preimage_iff : HasCompleteLift ι (σ ⁻¹' S) (sumExtend Y σ ⁻¹' T) ↔
    HasCompleteLift ι S T := by
  rw [hasCompleteLift_iff, hasCompleteLift_iff, hasLift_preimage_iff hσ,
    (sumExtend_surjective (Y := Y) hσ.2).forall]
  simp [isCompatibleNe_preimage_iff hσ, hasLiftNe_preimage_iff hσ]

/-- Genericity of a family of solutions is invariant under a change of coordinates: the image of
`Θ` under the word map of `σ` is generic for `σ ⁻¹' S` exactly when `Θ` is generic for `S`. -/
theorem isGenericFamily_preimage_image_iff {Θ : Set (X → H)} :
    IsGenericFamily ι (σ ⁻¹' S) (coordinateChangeEquiv ι σ hσ '' Θ) ↔ IsGenericFamily ι S Θ := by
  rw [isGenericFamily_iff, isGenericFamily_iff, ← image_coordinateChangeEquiv_V ι σ hσ,
    Set.image_subset_image_iff (coordinateChangeEquiv ι σ hσ).injective]
  refine and_congr_right fun _ => forall_congr' fun n => ?_
  rw [(sumExtend_surjective (Y := Fin n) hσ.2).forall]
  refine forall_congr' fun t => imp_congr (by simp) ?_
  rw [← hasCompleteLift_preimage_iff hσ, ← Set.image_singleton,
    (sumExtend_bijective hσ).1.preimage_image]

/-- The family of all solutions of the transformed system `σ ⁻¹' S` is generic exactly when the
family of all solutions of `S` is. -/
theorem isGenericFamily_preimage_V_iff :
    IsGenericFamily ι (σ ⁻¹' S) (V ι (σ ⁻¹' S)) ↔ IsGenericFamily ι S (V ι S) := by
  rw [← image_coordinateChangeEquiv_V ι σ hσ, isGenericFamily_preimage_image_iff hσ]

end TauCeti.GroupAlgGeom.Lift
