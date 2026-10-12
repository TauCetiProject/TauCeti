/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.SylowFour
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Dihedral
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# The two-by-two wreath product is dihedral of order eight

The faithful imprimitive action of `C₂ ≀ S₂` on four points has the label of the `4T3` reference
subgroup, which `TransitiveGroupLabel/Dihedral.lean` identifies with `DihedralGroup 4`
(`referenceSubgroupFourTwoMulEquivDihedralGroup`). Conjugating the action onto `4T3` therefore
gives an isomorphism from the wreath product to `DihedralGroup 4`.
-/

public section

open Equiv

namespace TauCeti

/-- A conjugator from the wreath product's four-point permutation image to `4T3`. -/
noncomputable def wreathTwoFourConjugator : Perm (Fin 4) :=
  Classical.choose ((transitiveGroupLabel_iff _ _).mp transitiveGroupLabel_wreathTwoToPermFour)

/-- The chosen conjugator carries the wreath product's permutation image onto `4T3`. -/
theorem wreathTwoToPermFour_range_map_conj_eq_referenceSubgroup :
    Subgroup.map (MulAut.conj wreathTwoFourConjugator).toMonoidHom
      wreathTwoToPermFour.range = referenceSubgroup 4 ⟨2, by simp⟩ :=
  Classical.choose_spec
    ((transitiveGroupLabel_iff _ _).mp transitiveGroupLabel_wreathTwoToPermFour)

/-- The two-by-two cyclic wreath product is dihedral of order eight. The isomorphism uses a
conjugation of its faithful four-point action onto the `4T3` reference subgroup. -/
noncomputable def wreathTwoMulEquivDihedralGroupFour :
    WreathProduct (Multiplicative (ZMod 2)) (Fin 2) ≃* DihedralGroup 4 := by
  let e₁ : WreathProduct (Multiplicative (ZMod 2)) (Fin 2) ≃*
      wreathTwoToPermFour.range :=
    MonoidHom.ofInjective wreathTwoToPermFour_injective
  let e₂ : wreathTwoToPermFour.range ≃* referenceSubgroup 4 ⟨2, by simp⟩ :=
    Subgroup.congrOfMapEq (MulAut.conj wreathTwoFourConjugator)
      wreathTwoToPermFour_range_map_conj_eq_referenceSubgroup
  exact (e₁.trans e₂).trans referenceSubgroupFourTwoMulEquivDihedralGroup

/-- The wreath-product isomorphism transports the four-point action by the chosen conjugator:
reading the image of `w` back in the `4T3` reference subgroup gives the conjugated action of
`w`. -/
@[simp]
theorem coe_referenceSubgroupFourTwoMulEquivDihedralGroup_symm_apply_wreath
    (w : WreathProduct (Multiplicative (ZMod 2)) (Fin 2)) :
    (referenceSubgroupFourTwoMulEquivDihedralGroup.symm
      (wreathTwoMulEquivDihedralGroupFour w) : Perm (Fin 4)) =
        (MulAut.conj wreathTwoFourConjugator) (wreathTwoToPermFour w) := by
  simp only [wreathTwoMulEquivDihedralGroupFour, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  refine (Subgroup.coe_congrOfMapEq_apply _ _ _).trans ?_
  rw [MonoidHom.ofInjective_apply]

end TauCeti
