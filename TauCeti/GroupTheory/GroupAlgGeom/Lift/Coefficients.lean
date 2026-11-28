/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.CoeffExtension
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic
import TauCeti.GroupTheory.GroupAlgGeom.Separated

/-!
# Lifts under a change of the coefficient group and of the further variables

Let `S ⊆ G[X]` be a system and `T = 1 ∧ W ≠ 1` a system with an inequation in the further
variables `Y`.

* Changing the coefficients along `f : G →* G'`: the image of the data over `G'`, solved through
  `ι : G' →* H`, is compatible with the image of `S` exactly when the data are compatible with
  `S` through `ι ∘ f`, and a lift of the data through `ι ∘ f`, with or without the inequation,
  gives a lift of their image.
* If `H` is separated by `G` over `G` through `ι : G →* H`, compatibility through `ι` descends
  to `G`; if moreover `ι` is injective, a lift through `ι`, with or without the inequation,
  exists exactly when a lift over `G` does, the two radicals of `S` being equal
  (`TauCeti.GroupAlgGeom.Rad_eq_of_isSeparatedBy`).
* Renaming the further variables along an injective `e : Z → Y` changes neither compatibility
  nor the existence of a lift.

With the finiteness of the letters and further variables occurring in finitely many words
(`TauCeti.GroupAlgGeom.GX.exists_finset_forall_mem_range_map_freeGroupMap`,
`TauCeti.GroupAlgGeom.GX.exists_finset_forall_mem_range_map_sumMap`), these are steps in reducing
lifting statements over a free group of arbitrary rank, with arbitrarily many further variables,
to a free factor of finite rank and finitely many further variables.

## Main results

* `TauCeti.GroupAlgGeom.Lift.isCompatibleNe_image_map_iff`,
  `TauCeti.GroupAlgGeom.Lift.HasLift.image_map`, `TauCeti.GroupAlgGeom.Lift.HasLiftNe.image_map`:
  change of the coefficient group.
* `TauCeti.GroupAlgGeom.Lift.IsCompatibleNe.of_isSeparatedBy`,
  `TauCeti.GroupAlgGeom.Lift.hasLift_iff_of_isSeparatedBy`,
  `TauCeti.GroupAlgGeom.Lift.hasLiftNe_iff_of_isSeparatedBy`: descent to a coefficient group by
  which the group of solutions is separated.
* `TauCeti.GroupAlgGeom.Lift.isCompatibleNe_image_map_sumMap_iff`,
  `TauCeti.GroupAlgGeom.Lift.hasLiftNe_image_map_sumMap_iff`: renaming the further variables.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §6, Definitions 25–27.
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

open Monoid.Coprod

variable {G G' H X Y Z : Type*} [Group G] [Group G'] [Group H]

section Coefficients

variable (f : G →* G') (ι : G' →* H) {S : Set (GX G X)} {T : Set (GX G (X ⊕ Y))}
  {W : GX G (X ⊕ Y)}

/-- Compatibility of `T = 1 ∧ W ≠ 1` with `S` through `ι ∘ f` is compatibility of their images
under the change of coefficients `f` through `ι`. -/
theorem isCompatibleNe_image_map_iff :
    IsCompatibleNe ι (Monoid.Coprod.map f (FreeGroup.map id) '' S)
        (Monoid.Coprod.map f (FreeGroup.map id) '' T) (Monoid.Coprod.map f (FreeGroup.map id) W) ↔
      IsCompatibleNe (ι.comp f) S T W := by
  simp [isCompatibleNe_iff, V_image_map]

variable {f ι}

/-- A lift of `T` to the generic point of `S` through `ι ∘ f` gives a lift of the images under the
change of coefficients `f`. -/
theorem HasLift.image_map (h : HasLift (ι.comp f) S T) :
    HasLift ι (Monoid.Coprod.map f (FreeGroup.map id) '' S)
      (Monoid.Coprod.map f (FreeGroup.map id) '' T) := by
  -- push the solution forward along the homomorphism of coordinate groups
  obtain ⟨w, hw⟩ := h.exists_sumElim_mem_V_of_gHom (CoordGroup.mapCoeff f ι S)
    CoordGroup.mapCoeff_comp_genericPoint
  exact hasLift_iff.2 ⟨w, by rwa [V_image_map]⟩

/-- A lift of `T = 1 ∧ W ≠ 1` to the generic point of `S` through `ι ∘ f` gives a lift of their
images under the change of coefficients `f`. -/
theorem HasLiftNe.image_map (h : HasLiftNe (ι.comp f) S T W) :
    HasLiftNe ι (Monoid.Coprod.map f (FreeGroup.map id) '' S)
      (Monoid.Coprod.map f (FreeGroup.map id) '' T) (Monoid.Coprod.map f (FreeGroup.map id) W) := by
  -- push the solution forward along the injective homomorphism of coordinate groups
  obtain ⟨w, hw, hW⟩ := h.exists_sumElim_mem_V_of_gHom (CoordGroup.mapCoeff f ι S)
    CoordGroup.mapCoeff_injective CoordGroup.mapCoeff_comp_genericPoint
  exact hasLiftNe_iff.2 ⟨w, by rwa [V_image_map], by rwa [eval_map, Function.comp_id]⟩

end Coefficients

section Separated

variable {ι : G →* H} {S : Set (GX G X)} {T : Set (GX G (X ⊕ Y))} {W : GX G (X ⊕ Y)}

/-- If `H` is separated by `G` over `G`, a system with an inequation that is compatible with `S`
through `ι` is compatible with `S` over `G`. -/
theorem IsCompatibleNe.of_isSeparatedBy (hH : IsSeparatedBy ι (.id G))
    (h : IsCompatibleNe ι S T W) : IsCompatibleNe (.id G) S T W := by
  refine isCompatibleNe_iff.2 fun v hv => ?_
  -- solve over the point `ι ∘ v` and retract the witness to `G`, keeping `W` nontrivial
  obtain ⟨w, hw, hW⟩ := isCompatibleNe_iff.1 h (ι ∘ v) ((GHom.mk ι fun _ => rfl).comp_mem_V hv)
  obtain ⟨ψ, hψ⟩ := (isSeparatedBy_def _ _).1 hH _ hW
  have hψv : ψ ∘ ι ∘ v = v := funext fun x => ψ.map_coeff (v x)
  refine ⟨ψ ∘ w, ?_, ?_⟩
  · simpa [Sum.comp_elim, hψv] using ψ.comp_mem_V hw
  · simpa [Sum.comp_elim, hψv] using hψ

/-- If `H` is separated by `G` over `G` through an injective `ι`, a system lifts to the generic
point of `S` through `ι` exactly when it lifts over `G`. -/
theorem hasLift_iff_of_isSeparatedBy (hι : Function.Injective ι) (hH : IsSeparatedBy ι (.id G)) :
    HasLift ι S T ↔ HasLift (.id G) S T :=
  hasLift_iff_of_Rad_eq (Rad_eq_of_isSeparatedBy hι hH S)

/-- If `H` is separated by `G` over `G` through an injective `ι`, a system with an inequation
lifts to the generic point of `S` through `ι` exactly when it lifts over `G`. -/
theorem hasLiftNe_iff_of_isSeparatedBy (hι : Function.Injective ι) (hH : IsSeparatedBy ι (.id G)) :
    HasLiftNe ι S T W ↔ HasLiftNe (.id G) S T W :=
  hasLiftNe_iff_of_Rad_eq (Rad_eq_of_isSeparatedBy hι hH S)

end Separated

section Variables

variable {ι : G →* H} {S : Set (GX G X)} {e : Z → Y} {T : Set (GX G (X ⊕ Z))} {W : GX G (X ⊕ Z)}

/-- Renaming the further variables along an injective map does not change compatibility. -/
theorem isCompatibleNe_image_map_sumMap_iff (he : Function.Injective e) :
    IsCompatibleNe ι S (Monoid.Coprod.map (.id G) (FreeGroup.map (Sum.map id e)) '' T)
        (Monoid.Coprod.map (.id G) (FreeGroup.map (Sum.map id e)) W) ↔
      IsCompatibleNe ι S T W := by
  rw [isCompatibleNe_iff, isCompatibleNe_iff]
  refine forall₂_congr fun v _ => ?_
  simp only [mem_V, Set.forall_mem_image, eval_map, MonoidHom.comp_id, Sum.elim_comp_map,
    Function.comp_id]
  -- a witness on `Z` extends along the injective `e` to a witness on `Y`
  refine ⟨fun ⟨w, hw⟩ => ⟨w ∘ e, hw⟩, fun ⟨w, hw⟩ => ?_⟩
  obtain ⟨w, rfl⟩ := he.surjective_comp_right w
  exact ⟨w, hw⟩

/-- Renaming the further variables along an injective map does not change the existence of a
lift. -/
theorem hasLiftNe_image_map_sumMap_iff (he : Function.Injective e) :
    HasLiftNe ι S (Monoid.Coprod.map (.id G) (FreeGroup.map (Sum.map id e)) '' T)
        (Monoid.Coprod.map (.id G) (FreeGroup.map (Sum.map id e)) W) ↔
      HasLiftNe ι S T W := by
  simp only [hasLiftNe_iff, mem_V, Set.forall_mem_image, eval_map, MonoidHom.comp_id,
    Sum.elim_comp_map, Function.comp_id]
  -- a solution on `Z` extends along the injective `e` to a solution on `Y`
  refine ⟨fun ⟨w, hw⟩ => ⟨w ∘ e, hw⟩, fun ⟨w, hw⟩ => ?_⟩
  obtain ⟨w, rfl⟩ := he.surjective_comp_right w
  exact ⟨w, hw⟩

end Variables

end TauCeti.GroupAlgGeom.Lift
