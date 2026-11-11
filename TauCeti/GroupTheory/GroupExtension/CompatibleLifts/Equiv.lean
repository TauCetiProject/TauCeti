/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.CompatibleLifts.Character

/-!
# Transport of compatible lifts

An equivalence of group extensions fixing the kernel and quotient transports compatible
lifts by conjugating their automorphisms of the middle group. It preserves the recorded
acting-group element and, for central extensions, the character twists.
-/

public section

namespace GroupExtension.Equiv

variable {N E E' G A : Type*} [Group N] [Group E] [Group E'] [Group G] [Group A]
  {S : GroupExtension N E G} {S' : GroupExtension N E' G}
  (F : S.Equiv S') (ρ : A →* MulAut G)

/-- Conjugation by an equivalence of extensions transports compatible lifts. -/
def compatibleLiftsMap : S.compatibleLifts ρ →* S'.compatibleLifts ρ :=
  (((MulAut.congr F.toMulEquiv).toMonoidHom.comp (compatibleLiftsToMulAut S ρ)).prod
    (compatibleLiftsProjection S ρ)).codRestrict _ fun x => by
      rw [MonoidHom.prod_apply, mem_compatibleLifts]
      constructor
      · intro n
        simp [MulAut.congr_apply, MulEquiv.trans_apply]
      · intro e
        simp [MulAut.congr_apply, MulEquiv.trans_apply]

@[simp]
theorem compatibleLiftsToMulAut_compatibleLiftsMap (x : S.compatibleLifts ρ) :
    compatibleLiftsToMulAut S' ρ (compatibleLiftsMap F ρ x) =
      MulAut.congr F.toMulEquiv (compatibleLiftsToMulAut S ρ x) :=
  compatibleLiftsToMulAut_apply S' ρ _

@[simp]
theorem compatibleLiftsProjection_compatibleLiftsMap (x : S.compatibleLifts ρ) :
    compatibleLiftsProjection S' ρ (compatibleLiftsMap F ρ x) = compatibleLiftsProjection S ρ x :=
  compatibleLiftsProjection_apply S' ρ _

theorem compatibleLiftsToMulAut_compatibleLiftsMap_apply (x : S.compatibleLifts ρ) (e : E') :
    compatibleLiftsToMulAut S' ρ (compatibleLiftsMap F ρ x) e =
      F (compatibleLiftsToMulAut S ρ x (F.symm e)) := by
  simp [MulAut.congr_apply, MulEquiv.trans_apply]

@[simp]
theorem compatibleLiftsMap_symm_map (x : S.compatibleLifts ρ) :
    compatibleLiftsMap F.symm ρ (compatibleLiftsMap F ρ x) = x := by
  apply compatibleLifts_ext S ρ
  · ext e
    rw [compatibleLiftsToMulAut_compatibleLiftsMap_apply,
      compatibleLiftsToMulAut_compatibleLiftsMap_apply]
    simp only [symm_apply_apply, apply_symm_apply]
  · rw [compatibleLiftsProjection_compatibleLiftsMap, compatibleLiftsProjection_compatibleLiftsMap]

@[simp]
theorem compatibleLiftsMap_map_symm (x : S'.compatibleLifts ρ) :
    compatibleLiftsMap F ρ (compatibleLiftsMap F.symm ρ x) = x := by
  simpa only [symm_symm] using compatibleLiftsMap_symm_map F.symm ρ x

/-- Equivalent extensions have equivalent groups of compatible lifts. -/
def compatibleLiftsCongr : S.compatibleLifts ρ ≃* S'.compatibleLifts ρ where
  toFun := compatibleLiftsMap F ρ
  invFun := compatibleLiftsMap F.symm ρ
  left_inv := compatibleLiftsMap_symm_map F ρ
  right_inv := compatibleLiftsMap_map_symm F ρ
  map_mul' := (compatibleLiftsMap F ρ).map_mul

@[simp]
theorem compatibleLiftsCongr_apply (x : S.compatibleLifts ρ) :
    compatibleLiftsCongr F ρ x = compatibleLiftsMap F ρ x :=
  (rfl)

@[simp]
theorem compatibleLiftsCongr_symm_apply (x : S'.compatibleLifts ρ) :
    (compatibleLiftsCongr F ρ).symm x = compatibleLiftsMap F.symm ρ x :=
  (rfl)

end GroupExtension.Equiv

namespace GroupExtension.Equiv

variable {N E E' G A : Type*} [CommGroup N] [Group E] [Group E'] [Group G] [Group A]
  {S : GroupExtension N E G} {S' : GroupExtension N E' G}
  (F : S.Equiv S') (ρ : A →* MulAut G) (hcentral : S.inl.range ≤ Subgroup.center E)

@[simp]
theorem compatibleLiftsMap_compatibleLiftsCharacterTwist (χ : G →* N) :
    compatibleLiftsMap F ρ (compatibleLiftsCharacterTwist S ρ hcentral χ) =
      compatibleLiftsCharacterTwist S' ρ (F.inl_range_le_center hcentral) χ := by
  apply compatibleLifts_ext S' ρ
  · rw [compatibleLiftsToMulAut_compatibleLiftsMap,
      compatibleLiftsToMulAut_compatibleLiftsCharacterTwist,
      compatibleLiftsToMulAut_compatibleLiftsCharacterTwist, mulAutCongr_characterTwist]
  · rw [compatibleLiftsProjection_compatibleLiftsMap,
      compatibleLiftsProjection_compatibleLiftsCharacterTwist,
      compatibleLiftsProjection_compatibleLiftsCharacterTwist]

end GroupExtension.Equiv
