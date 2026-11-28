/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.DegreeRatio
public import TauCeti.RepresentationTheory.Induction.Mackey.Quaternion.Basic
public import TauCeti.RepresentationTheory.Induction.LinearCharacter

/-!
# The degree ratio over the centre of `Q₈`

For `G = Q₈`, `N = Z(Q₈) = {1, a 2}` and `θ` its faithful linear character, the two-dimensional
irreducible representation `W` of `Q₈`, induced from the character of the rotation subgroup
sending `a 1` to `i`, lies over `θ`. The degree ratio `dim W / dim θ = 2` divides `|G : N| = 4`
(`FDRep.finrank_dvd_finrank_and_finrank_div_finrank_dvd_index_of_liesOver`). Since `N` is central,
`θ` is invariant and its inertia group is all of `Q₈`, so the ratio is not the index `1` of the
inertia group: it is the dimension of the multiplicity space, a projective representation of
`Q₈ / N ≅ C₂ × C₂`.
-/

public section

open TauCeti

namespace TauCeti.Examples.DegreeRatioQuaternion

/-- The faithful linear character `θ` of the centre of `Q₈`: the restriction of the rotation
character sending `a 1` to `i`, so `θ (a 2) = -1`. -/
noncomputable def centerChar : Subgroup.center (QuaternionGroup 2) →* ℂˣ :=
  quaternionGroupTwoRotationChar.comp
    (Subgroup.inclusion (center_quaternionGroup_le_quaternionRotations (by decide)))

/-- The two-dimensional irreducible representation `W` of `Q₈`. -/
noncomputable abbrev twoDimRep : FDRep ℂ (QuaternionGroup 2) :=
  indFDRep (FDRep.ofLinearCharacter quaternionGroupTwoRotationChar)

/-- `θ` is faithful: it takes the value `-1` at `a 2`. -/
example : (centerChar ⟨QuaternionGroup.a 2, quaternionGroup_a_self_mem_center 2⟩ : ℂ) = -1 := by
  -- Mathlib has `SubgroupClass.inclusion_mk` but no `Subgroup.inclusion_mk`, so the inclusion
  -- of `⟨a 2, _⟩` is computed from `Subgroup.coe_inclusion`.
  rw [centerChar, MonoidHom.comp_apply,
    show Subgroup.inclusion (K := quaternionRotations 2) _
        ⟨QuaternionGroup.a 2, quaternionGroup_a_self_mem_center 2⟩ =
        ⟨QuaternionGroup.a 2, a_mem_quaternionRotations 2⟩ from
      Subtype.ext (Subgroup.coe_inclusion _ _),
    coe_quaternionGroupTwoRotationChar_a, ZMod.val_two_eq_two_mod]
  norm_num [Complex.I_sq]

/-- `W` lies over `θ`. -/
theorem liesOver_twoDimRep : FDRep.LiesOver twoDimRep (Subgroup.center (QuaternionGroup 2)).subtype
    (FDRep.ofLinearCharacter centerChar) := by
  have : Nontrivial (FDRep.ofLinearCharacter (k := ℂ) quaternionGroupTwoRotationChar) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp)
  have h := (FDRep.liesOver_res_self (FDRep.ofLinearCharacter quaternionGroupTwoRotationChar)
    (Subgroup.inclusion
      (center_quaternionGroup_le_quaternionRotations (by decide)))).indFDRep
  rw [Subgroup.subtype_comp_inclusion, FDRep.actionRes_obj_ofLinearCharacter] at h
  exact h

/-- The inertia group of `θ` is all of `Q₈`, since `θ` is a character of the centre. -/
theorem inertia_centerChar :
    inertia (G := QuaternionGroup 2) (FDRep.ofLinearCharacter centerChar) = ⊤ := by
  refine eq_top_iff.2 fun g _ => mem_inertia_iff_forall_char_conj_eq.2 fun x => ?_
  congr 1
  ext
  rw [Subgroup.coe_mk, mul_assoc, ← Subgroup.mem_center_iff.1 x.property g, inv_mul_cancel_left]

/-- **The degree ratio over the centre of `Q₈`** is `2`, which divides `|Q₈ : Z(Q₈)| = 4` but is
not the index `1` of the inertia group of `θ`. -/
example : Module.finrank ℂ twoDimRep / Module.finrank ℂ (FDRep.ofLinearCharacter centerChar) = 2 ∧
    (Subgroup.center (QuaternionGroup 2)).index = 4 ∧
    (inertia (G := QuaternionGroup 2) (FDRep.ofLinearCharacter centerChar)).index = 1 := by
  refine ⟨?_, index_center_quaternionGroup (by decide), by
    rw [inertia_centerChar, Subgroup.index_top]⟩
  rw [finrank_indFDRep_ofLinearCharacter, index_quaternionRotations,
    FDRep.finrank_ofLinearCharacter]

-- The general theorem applies.
example : Module.finrank ℂ twoDimRep / Module.finrank ℂ (FDRep.ofLinearCharacter centerChar) ∣
    (Subgroup.center (QuaternionGroup 2)).index :=
  have := simple_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar
  (FDRep.finrank_dvd_finrank_and_finrank_div_finrank_dvd_index_of_liesOver _ twoDimRep
    liesOver_twoDimRep).2

end TauCeti.Examples.DegreeRatioQuaternion
