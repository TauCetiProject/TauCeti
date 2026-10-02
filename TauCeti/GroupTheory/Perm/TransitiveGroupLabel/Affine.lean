/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Field.ZMod
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification
public import TauCeti.GroupTheory.SpecificGroups.Affine.Basic

/-!
# The Frobenius reference permutation group in degree five

The reference subgroup `5T3` is the Frobenius group `F₂₀` of order twenty. It is the affine group
`AGL(1, 5)` of the field `ZMod 5` acting on its five points, which are numbered by `Fin 5` through
`ZMod.finEquiv 5`. In that numbering the five-cycle `finRotate 5` is the translation `x ↦ x + 1`
and the four-cycle `[0, 1, 3, 2].formPerm` is the affine map `x ↦ 2 x + 1`.

The affine group acts faithfully on `ZMod 5`, so it embeds into the permutations of `Fin 5`. Its
image contains both generators of the reference subgroup, and both groups have order twenty, so
the image is exactly the reference subgroup.

## Main results

* `TauCeti.referenceSubgroupFiveTwoMulEquivAffineGroup`: the reference subgroup of `5T3` is
  isomorphic to `TauCeti.AffineGroup (ZMod 5)`, compatibly with the two actions on five points.
* `TauCeti.TransitiveGroupLabel.nonempty_mulEquiv_affineGroup_five_two`: every permutation group
  with label `5T3` is abstractly `AGL(1, 5)`.
-/

public section

open Equiv Equiv.Perm

namespace TauCeti

/-- The permutation of `Fin 5` by which an affine map of `ZMod 5` acts. -/
private noncomputable def affinePermHom : AffineGroup (ZMod 5) →* Perm (Fin 5) :=
  ((ZMod.finEquiv 5).toEquiv.symm.permCongrHom : Perm (ZMod 5) →* Perm (Fin 5)).comp
    (MulAction.toPermHom (AffineGroup (ZMod 5)) (ZMod 5))

private theorem affinePermHom_apply (g : AffineGroup (ZMod 5)) (i : Fin 5) :
    affinePermHom g i = (ZMod.finEquiv 5).symm (g • ZMod.finEquiv 5 i) :=
  (rfl)

private theorem affinePermHom_injective : Function.Injective affinePermHom :=
  (MulEquiv.injective (ZMod.finEquiv 5).toEquiv.symm.permCongrHom).comp
    MulAction.toPerm_injective

private theorem range_affinePermHom :
    affinePermHom.range = referenceSubgroup 5 ⟨2, by simp⟩ := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rw [referenceSubgroup_five_two, Subgroup.closure_le]
    rintro σ (rfl | rfl)
    · refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd 1), Equiv.ext fun i ↦ ?_⟩
      rw [affinePermHom_apply]
      fin_cases i <;> rfl
    · refine ⟨⟨Multiplicative.ofAdd 1, ZMod.unitOfCoprime 2 (by norm_num)⟩,
        Equiv.ext fun i ↦ ?_⟩
      rw [affinePermHom_apply]
      fin_cases i <;> rfl
  · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    rw [natCard_referenceSubgroup_five_two,
      ← Nat.card_congr (MonoidHom.ofInjective affinePermHom_injective).toEquiv]
    exact (card_affineGroup (ZMod 5)).trans_le (by rw [Nat.card_zmod])

/-- **The reference subgroup `5T3` is the affine group `AGL(1, 5)`.** The isomorphism is
compatible with the two actions on five points, numbered through `ZMod.finEquiv 5`; see
`TauCeti.referenceSubgroupFiveTwoMulEquivAffineGroup_smul`. -/
noncomputable def referenceSubgroupFiveTwoMulEquivAffineGroup :
    referenceSubgroup 5 ⟨2, by simp⟩ ≃* AffineGroup (ZMod 5) :=
  ((MonoidHom.ofInjective affinePermHom_injective).trans
    (MulEquiv.subgroupCongr range_affinePermHom)).symm

/-- The permutation of `Fin 5` attached to an affine map of `ZMod 5` is that affine map, read
through `ZMod.finEquiv 5`. -/
@[simp]
theorem coe_referenceSubgroupFiveTwoMulEquivAffineGroup_symm_apply (g : AffineGroup (ZMod 5))
    (i : Fin 5) :
    (referenceSubgroupFiveTwoMulEquivAffineGroup.symm g : Perm (Fin 5)) i =
      (ZMod.finEquiv 5).symm (g • ZMod.finEquiv 5 i) := by
  rw [← affinePermHom_apply]
  simp [referenceSubgroupFiveTwoMulEquivAffineGroup, MonoidHom.ofInjective_apply]

/-- The affine map attached to a permutation in `5T3` acts on `ZMod 5` as the permutation acts on
`Fin 5`. -/
@[simp]
theorem referenceSubgroupFiveTwoMulEquivAffineGroup_smul (σ : referenceSubgroup 5 ⟨2, by simp⟩)
    (i : Fin 5) :
    referenceSubgroupFiveTwoMulEquivAffineGroup σ • ZMod.finEquiv 5 i =
      ZMod.finEquiv 5 ((σ : Perm (Fin 5)) i) := by
  conv_rhs => rw [← referenceSubgroupFiveTwoMulEquivAffineGroup.symm_apply_apply σ]
  rw [coe_referenceSubgroupFiveTwoMulEquivAffineGroup_symm_apply, RingEquiv.apply_symm_apply]

/-- The five-cycle of `5T3` is the translation `x ↦ x + 1`. -/
@[simp]
theorem referenceSubgroupFiveTwoMulEquivAffineGroup_apply_finRotate :
    referenceSubgroupFiveTwoMulEquivAffineGroup
        ⟨finRotate 5, by
          rw [referenceSubgroup_five_two]
          exact Subgroup.subset_closure (by simp)⟩ =
      SemidirectProduct.inl (Multiplicative.ofAdd 1) := by
  apply referenceSubgroupFiveTwoMulEquivAffineGroup.symm.injective
  ext i
  rw [MulEquiv.symm_apply_apply, coe_referenceSubgroupFiveTwoMulEquivAffineGroup_symm_apply]
  fin_cases i <;> rfl

/-- The four-cycle of `5T3` is the affine map `x ↦ 2 x + 1`. -/
theorem referenceSubgroupFiveTwoMulEquivAffineGroup_apply_formPerm :
    referenceSubgroupFiveTwoMulEquivAffineGroup
        ⟨[0, 1, 3, 2].formPerm, by
          rw [referenceSubgroup_five_two]
          exact Subgroup.subset_closure (by simp)⟩ =
      ⟨Multiplicative.ofAdd 1, ZMod.unitOfCoprime 2 (by norm_num)⟩ := by
  apply referenceSubgroupFiveTwoMulEquivAffineGroup.symm.injective
  ext i
  rw [MulEquiv.symm_apply_apply, coe_referenceSubgroupFiveTwoMulEquivAffineGroup_symm_apply]
  fin_cases i <;> rfl

/-- Every permutation subgroup with label `5T3` is abstractly the affine group `AGL(1, 5)`. The
isomorphism depends on the conjugating permutation used to read the label. -/
theorem TransitiveGroupLabel.nonempty_mulEquiv_affineGroup_five_two
    {G : Subgroup (Perm (Fin 5))}
    (h : TransitiveGroupLabel (⟨2, by simp⟩ : TransitiveGroupIndex 5) G) :
    Nonempty (G ≃* AffineGroup (ZMod 5)) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_referenceSubgroup
  exact ⟨e.trans referenceSubgroupFiveTwoMulEquivAffineGroup⟩

end TauCeti
