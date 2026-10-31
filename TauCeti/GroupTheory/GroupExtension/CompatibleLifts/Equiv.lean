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

/-- Conjugation by a native extension equivalence transports compatible lifts. -/
def compatibleLiftsMap : S.compatibleLifts ρ →* S'.compatibleLifts ρ where
  toFun x := ⟨(MulAut.congr F.toMulEquiv (compatibleLiftsToMulAut S ρ x),
    compatibleLiftsProjection S ρ x), by
    rw [mem_compatibleLifts]
    constructor
    · intro n
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    · intro e
      simp [MulAut.congr_apply, MulEquiv.trans_apply]⟩
  map_one' := by
    apply compatibleLifts_ext S' ρ
    · simpa only [compatibleLiftsToMulAut_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        OneMemClass.coe_one, Prod.fst_one] using
        ((MulAut.congr F.toMulEquiv).toMonoidHom.comp (compatibleLiftsToMulAut S ρ)).map_one
    · simp only [compatibleLiftsProjection_apply, OneMemClass.coe_one, Prod.snd_one]
  map_mul' x y := by
    apply compatibleLifts_ext S' ρ
    · simp only [map_mul, compatibleLiftsToMulAut_apply]
    · simp only [map_mul, compatibleLiftsProjection_apply]

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

/-- Equivalent extensions have equivalent groups of compatible lifts. -/
def compatibleLiftsCongr : S.compatibleLifts ρ ≃* S'.compatibleLifts ρ where
  toFun := compatibleLiftsMap F ρ
  invFun := compatibleLiftsMap F.symm ρ
  left_inv := compatibleLiftsMap_symm_map F ρ
  right_inv x := by
    simpa only [symm_symm] using compatibleLiftsMap_symm_map F.symm ρ x
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
theorem compatibleLiftsMap_character (χ : G →* N) :
    compatibleLiftsMap F ρ (compatibleLiftsCharacter S ρ hcentral χ) =
      compatibleLiftsCharacter S' ρ (F.inl_range_le_center hcentral) χ := by
  apply compatibleLifts_ext S' ρ
  · rw [compatibleLiftsToMulAut_compatibleLiftsMap, compatibleLiftsToMulAut_character,
    compatibleLiftsToMulAut_character, mulAutCongr_twist]
  · rw [compatibleLiftsProjection_compatibleLiftsMap, compatibleLiftsProjection_character,
    compatibleLiftsProjection_character]

end GroupExtension.Equiv
