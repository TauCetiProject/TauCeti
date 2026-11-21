/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Alternating.KleinFour
public import TauCeti.GroupTheory.Complement.CrossedProjection
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Crossed projections and local complements for the Klein four-group in `A₄` and `S₄`

This file builds on `TauCeti.GroupTheory.SpecificGroups.Alternating.KleinFour` to compute the
crossed projections and local complements associated with `alternatingGroup.kleinFour α` when
`Nat.card α = 4`.

Along the point stabilizer `MulAction.stabilizer (alternatingGroup α) a`, the crossed projection
`alternatingGroup α → alternatingGroup.kleinFour α` sends `g` to the unique element of
`alternatingGroup.kleinFour α` carrying `a` to `g • a`
(`TauCeti.crossedProjection_isComplement'_kleinFour_stabilizer`). Translating `a` by
`v ∈ alternatingGroup.kleinFour α` shifts the crossed projection by the principal crossed map
`g ↦ g • v / v` (`TauCeti.crossedProjection_isComplement'_kleinFour_stabilizer_smul`), and
`a ↦ crossedProjection (Stab a)` identifies `α` with the four normalized additive crossed maps
(`TauCeti.kleinFourCrossedProjectionEquiv`).

Inside `Equiv.Perm α`, the local complements of
`(alternatingGroup.kleinFour α).map (alternatingGroup α).subtype` in `alternatingGroup α` are
precisely the subgroups `MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α`
(`TauCeti.isLocalComplement_map_subtype_kleinFour_iff_exists_stabilizer`), and each is the unique
such local complement normalized by `MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α`
(`TauCeti.isLocalComplement_map_subtype_kleinFour_and_le_normalizer_iff`).

## Main definitions

* `TauCeti.kleinFourCrossedProjectionEquiv`: the bijection between `α` and the normalized additive
  crossed maps `alternatingGroup α → Additive (alternatingGroup.kleinFour α)`.

## Main results

* `TauCeti.crossedProjection_isComplement'_kleinFour_stabilizer`,
  `TauCeti.crossedProjection_isComplement'_kleinFour_stabilizer_smul`: explicit evaluation of the
  crossed projection along a point stabilizer and its transformation under conjugation by
  `alternatingGroup.kleinFour α`.
* `TauCeti.card_kleinFour_crossedProjection`: there are exactly four normalized additive crossed
  maps `alternatingGroup α → Additive (alternatingGroup.kleinFour α)`.
* `TauCeti.isLocalComplement_map_subtype_kleinFour_iff_exists_stabilizer`,
  `TauCeti.isLocalComplement_map_subtype_kleinFour_and_le_normalizer_iff`: classification and
  uniqueness of the local complement of `alternatingGroup.kleinFour α` in `alternatingGroup α`
  (inside `Equiv.Perm α`) normalized by `MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α`.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
-/

public section

open Equiv Equiv.Perm
open scoped IsMulCommutative Pointwise

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Crossed projections along point stabilizers -/

section CrossedProjection

attribute [local instance] Subgroup.conjugationAction

/-- Along `MulAction.stabilizer (alternatingGroup α) a`, the crossed projection of `g` onto
`alternatingGroup.kleinFour α` is the unique element of `alternatingGroup.kleinFour α` sending `a`
to `g • a`. -/
theorem crossedProjection_isComplement'_kleinFour_stabilizer (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) :
    (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection g =
      (kleinFourEquiv hα4 a).symm (g • a) := by
  obtain ⟨⟨n, d⟩, rfl⟩ := (isComplement'_kleinFour_stabilizer hα4 a).surjective g
  dsimp only
  rw [Subgroup.IsComplement'.crossedProjection_mul, eq_comm, kleinFourEquiv_symm_eq_iff]
  have hd : (d : alternatingGroup α) • a = a := MulAction.mem_stabilizer_iff.mp d.property
  rw [mul_smul, hd, Subgroup.smul_def]

/-- Applying the crossed projection of `g` along `MulAction.stabilizer (alternatingGroup α) a` to
`a` agrees with `g • a`. -/
theorem crossedProjection_isComplement'_kleinFour_stabilizer_apply_smul (hα4 : Nat.card α = 4)
    (a : α) (g : alternatingGroup α) :
    (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection g • a = g • a := by
  rw [crossedProjection_isComplement'_kleinFour_stabilizer hα4 a g, kleinFourEquiv_symm_apply_smul]

/-- The crossed projection of `g` along `MulAction.stabilizer (alternatingGroup α) a` equals `v`
if and only if `v • a = g • a`. -/
theorem crossedProjection_isComplement'_kleinFour_stabilizer_eq_iff (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) (v : alternatingGroup.kleinFour α) :
    (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection g = v ↔ v • a = g • a := by
  rw [crossedProjection_isComplement'_kleinFour_stabilizer hα4 a g, kleinFourEquiv_symm_eq_iff,
    eq_comm]

/-- Translating the base point `a` by `v ∈ alternatingGroup.kleinFour α` multiplies the crossed
projection along `MulAction.stabilizer (alternatingGroup α) a` by the principal crossed map
`g ↦ g • v / v`. -/
theorem crossedProjection_isComplement'_kleinFour_stabilizer_smul (hα4 : Nat.card α = 4) (a : α)
    (v : alternatingGroup.kleinFour α) (g : alternatingGroup α) :
    (isComplement'_kleinFour_stabilizer hα4 (v • a)).crossedProjection g =
      (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection g * (g • v / v) := by
  have := isMulCommutative_kleinFour hα4.le
  have hconj : MulAction.stabilizer (alternatingGroup α) (v • a) =
      MulAut.conj (v : alternatingGroup α) • MulAction.stabilizer (alternatingGroup α) a := by
    rw [Subgroup.smul_def, stabilizer_smul_eq_conj_smul]
  exact ((isComplement'_kleinFour_stabilizer hα4 a).eq_conj_smul_iff_crossedProjection_eq
    (isComplement'_kleinFour_stabilizer hα4 (v • a)) v).mp hconj g

/-- When `Nat.card α = 4`, sending `a : α` to the crossed projection along
`MulAction.stabilizer (alternatingGroup α) a` identifies `α` with the normalized additive crossed
maps `alternatingGroup α → Additive (alternatingGroup.kleinFour α)`. -/
noncomputable def kleinFourCrossedProjectionEquiv (hα4 : Nat.card α = 4)
    [IsMulCommutative (alternatingGroup.kleinFour α)] :
    α ≃ {c : alternatingGroup α → Additive (alternatingGroup.kleinFour α) //
      groupCohomology.IsCocycle₁ c ∧
        ∀ n : alternatingGroup.kleinFour α, c n = Additive.ofMul n} :=
  (kleinFourComplementEquiv hα4).trans (alternatingGroup.kleinFour α).crossedProjectionEquiv

/-- The normalized additive crossed map attached to `a : α` sends `g` to the unique element of
`alternatingGroup.kleinFour α` carrying `a` to `g • a`, read additively. -/
@[simp]
theorem coe_kleinFourCrossedProjectionEquiv_apply (hα4 : Nat.card α = 4)
    [IsMulCommutative (alternatingGroup.kleinFour α)] (a : α) (g : alternatingGroup α) :
    (kleinFourCrossedProjectionEquiv hα4 a).val g =
      Additive.ofMul ((kleinFourEquiv hα4 a).symm (g • a)) := by
  have hEq : kleinFourComplementEquiv hα4 a =
      ⟨MulAction.stabilizer (alternatingGroup α) a, isComplement'_kleinFour_stabilizer hα4 a⟩ :=
    Subtype.ext (coe_kleinFourComplementEquiv_apply hα4 a)
  rw [kleinFourCrossedProjectionEquiv, Equiv.trans_apply, hEq,
    Subgroup.crossedProjectionEquiv_apply]
  exact congrArg Additive.ofMul (crossedProjection_isComplement'_kleinFour_stabilizer hα4 a g)

/-- The zero locus of the normalized additive crossed map attached to `a : α` is the point
stabilizer of `a`. -/
@[simp]
theorem zeroLocus_kleinFourCrossedProjectionEquiv_apply (hα4 : Nat.card α = 4)
    [IsMulCommutative (alternatingGroup.kleinFour α)] (a : α) :
    groupCohomology.zeroLocus (kleinFourCrossedProjectionEquiv hα4 a).property.1 =
      MulAction.stabilizer (alternatingGroup α) a := by
  rw [kleinFourCrossedProjectionEquiv, Equiv.trans_apply,
    ← Subgroup.crossedProjectionEquiv_symm_apply, Equiv.symm_apply_apply,
    coe_kleinFourComplementEquiv_apply]

/-- The inverse of `TauCeti.kleinFourCrossedProjectionEquiv` recovers the fixed point whose
stabilizer is the zero locus of a normalized additive crossed map. -/
@[simp]
theorem stabilizer_kleinFourCrossedProjectionEquiv_symm_apply (hα4 : Nat.card α = 4)
    [IsMulCommutative (alternatingGroup.kleinFour α)]
    (c : {c : alternatingGroup α → Additive (alternatingGroup.kleinFour α) //
      groupCohomology.IsCocycle₁ c ∧
        ∀ n : alternatingGroup.kleinFour α, c n = Additive.ofMul n}) :
    MulAction.stabilizer (alternatingGroup α) ((kleinFourCrossedProjectionEquiv hα4).symm c) =
      groupCohomology.zeroLocus c.property.1 := by
  rw [kleinFourCrossedProjectionEquiv, Equiv.symm_trans_apply,
    stabilizer_kleinFourComplementEquiv_symm_apply, Subgroup.crossedProjectionEquiv_symm_apply]

/-- `(kleinFourCrossedProjectionEquiv hα4).symm c` is `a` if and only if the zero locus of `c` is
the stabilizer of `a`. -/
theorem kleinFourCrossedProjectionEquiv_symm_eq_iff (hα4 : Nat.card α = 4)
    [IsMulCommutative (alternatingGroup.kleinFour α)]
    (c : {c : alternatingGroup α → Additive (alternatingGroup.kleinFour α) //
      groupCohomology.IsCocycle₁ c ∧
        ∀ n : alternatingGroup.kleinFour α, c n = Additive.ofMul n})
    (a : α) :
    (kleinFourCrossedProjectionEquiv hα4).symm c = a ↔
      groupCohomology.zeroLocus c.property.1 = MulAction.stabilizer (alternatingGroup α) a := by
  rw [kleinFourCrossedProjectionEquiv, Equiv.symm_trans_apply,
    kleinFourComplementEquiv_symm_eq_iff, Subgroup.crossedProjectionEquiv_symm_apply]

/-- When `Nat.card α = 4`, there are exactly four normalized additive crossed maps
`alternatingGroup α → Additive (alternatingGroup.kleinFour α)`. -/
theorem card_kleinFour_crossedProjection (hα4 : Nat.card α = 4)
    [IsMulCommutative (alternatingGroup.kleinFour α)] :
    Nat.card {c : alternatingGroup α → Additive (alternatingGroup.kleinFour α) //
      groupCohomology.IsCocycle₁ c ∧
        ∀ n : alternatingGroup.kleinFour α, c n = Additive.ofMul n} = 4 :=
  (Nat.card_congr (kleinFourCrossedProjectionEquiv hα4).symm).trans hα4

end CrossedProjection

/-! ### Local complements of `V₄` in `alternatingGroup α` inside `Equiv.Perm α` -/

/-- When `Nat.card α = 4`, the local complements of
`(alternatingGroup.kleinFour α).map (alternatingGroup α).subtype` in `alternatingGroup α` (inside
`Equiv.Perm α`) are precisely the subgroups
`MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α`. -/
theorem isLocalComplement_map_subtype_kleinFour_iff_exists_stabilizer (hα4 : Nat.card α = 4)
    {K : Subgroup (Perm α)} :
    ((alternatingGroup.kleinFour α).map (alternatingGroup α).subtype).IsLocalComplement K
        (alternatingGroup α) ↔
      ∃ a : α, K = MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α := by
  have hN_le : (alternatingGroup.kleinFour α).map (alternatingGroup α).subtype ≤
      alternatingGroup α := Subgroup.map_subtype_le _
  have hN_sub : ((alternatingGroup.kleinFour α).map (alternatingGroup α).subtype).subgroupOf
      (alternatingGroup α) = alternatingGroup.kleinFour α := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective (alternatingGroup α).subtype_injective _
  refine ⟨fun hK => ?_, ?_⟩
  · have hcomp : (alternatingGroup.kleinFour α).IsComplement'
        (K.subgroupOf (alternatingGroup α)) :=
      hN_sub ▸ (Subgroup.isLocalComplement_iff_isComplement'_subgroupOf hN_le hK.right_le).mp hK
    obtain ⟨a, ha⟩ := (isComplement'_kleinFour_iff_exists_stabilizer hα4).mp hcomp
    refine ⟨a, ?_⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hK.right_le, ha,
      ← MulAction.stabilizer_subgroupOf, Subgroup.subgroupOf_map_subtype]
  · rintro ⟨a, rfl⟩
    rw [← Subgroup.subgroupOf_map_subtype, MulAction.stabilizer_subgroupOf]
    have hm := (Subgroup.isLocalComplement_top_iff.mpr
      (isComplement'_kleinFour_stabilizer hα4 a)).map (alternatingGroup α).subtype_injective
    simpa only [Subgroup.map_top, Subgroup.range_subtype] using hm

/-- When `Nat.card α = 4`, `MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α` is the unique
local complement of `(alternatingGroup.kleinFour α).map (alternatingGroup α).subtype` in
`alternatingGroup α` normalized by `MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α`. -/
theorem isLocalComplement_map_subtype_kleinFour_and_le_normalizer_iff (hα4 : Nat.card α = 4)
    (a : α) {K : Subgroup (Perm α)} :
    ((alternatingGroup.kleinFour α).map (alternatingGroup α).subtype).IsLocalComplement K
        (alternatingGroup α) ∧
        MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α ≤ Subgroup.normalizer K ↔
      K = MulAction.stabilizer (Perm α) a ⊓ alternatingGroup α := by
  refine ⟨fun ⟨hK, hnorm⟩ => ?_, ?_⟩
  · obtain ⟨b, rfl⟩ :=
      (isLocalComplement_map_subtype_kleinFour_iff_exists_stabilizer hα4).mp hK
    have hnorm' : MulAction.stabilizer (alternatingGroup α) a ≤
        Subgroup.normalizer (MulAction.stabilizer (alternatingGroup α) b) := by
      have hsub := Subgroup.subgroupOf_mono (alternatingGroup α) hnorm
      rwa [Subgroup.subgroupOf_normalizer_eq inf_le_right, Subgroup.inf_subgroupOf_right,
        Subgroup.inf_subgroupOf_right, MulAction.stabilizer_subgroupOf,
        MulAction.stabilizer_subgroupOf] at hsub
    have heq := (isComplement'_kleinFour_and_stabilizer_le_normalizer_iff hα4 a).mp
      ⟨isComplement'_kleinFour_stabilizer hα4 b, hnorm'⟩
    rw [← Subgroup.subgroupOf_map_subtype, MulAction.stabilizer_subgroupOf, heq,
      ← MulAction.stabilizer_subgroupOf, Subgroup.subgroupOf_map_subtype]
  · rintro rfl
    exact ⟨(isLocalComplement_map_subtype_kleinFour_iff_exists_stabilizer hα4).mpr ⟨a, rfl⟩,
      Subgroup.le_normalizer⟩

end TauCeti
