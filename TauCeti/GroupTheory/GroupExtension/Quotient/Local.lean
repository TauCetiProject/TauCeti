/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Local
public import TauCeti.GroupTheory.GroupExtension.Quotient.Basic

/-!
# Local complements and quotient splittings

For subgroups `N ≤ H`, with `N` normal inside `H`, splittings of the quotient extension
of `H` by `N.subgroupOf H` correspond to local complements of `N` in `H`, viewed as
subgroups of the original ambient group. No normality in the ambient group, commutativity,
or finiteness is needed.

`Subgroup.localQuotientSplittingEquiv` combines the global quotient-splitting dictionary
with the passage between subgroups of `H` and subgroups of the ambient group contained in `H`.
Its inverse recovers the right projection of the local product decomposition; the left
projection is the remainder after removing that splitting value.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] (N H : Subgroup G) [(N.subgroupOf H).Normal]

/-- Splittings of the quotient extension inside `H` correspond to local complements of `N`
in `H`, as subgroups of the ambient group. -/
noncomputable def localQuotientSplittingEquiv (hNH : N ≤ H) :
    (N.subgroupOf H).quotientExtension.Splitting ≃
      {K : Subgroup G // N.IsLocalComplement K H} where
  toFun s := ⟨s.toMonoidHom.range.map H.subtype, by
    have h := (isLocalComplement_top_iff.mpr s.isComplement'_range_quotientExtension).map
      H.subtype_injective
    simpa only [map_subgroupOf_eq_of_le hNH, map_top, range_subtype] using h⟩
  invFun K := K.property.isComplement'_subgroupOf.quotientSplitting
  left_inv s := by
    apply GroupExtension.Splitting.eq_of_range_eq
    rw [IsComplement'.range_quotientSplitting]
    exact comap_map_eq_self_of_injective H.subtype_injective s.toMonoidHom.range
  right_inv K := by
    apply Subtype.ext
    exact (congrArg (Subgroup.map H.subtype)
      K.property.isComplement'_subgroupOf.range_quotientSplitting).trans
        (map_subgroupOf_eq_of_le K.property.right_le)

/-- The local complement associated to a splitting is its range in the original group. -/
@[simp]
theorem localQuotientSplittingEquiv_apply_coe (hNH : N ≤ H)
    (s : (N.subgroupOf H).quotientExtension.Splitting) :
    (N.localQuotientSplittingEquiv H hNH s).val = s.toMonoidHom.range.map H.subtype := (rfl)

/-- The splitting associated to a local complement is the quotient splitting inside `H`. -/
@[simp]
theorem localQuotientSplittingEquiv_symm_apply (hNH : N ≤ H)
    (K : {K : Subgroup G // N.IsLocalComplement K H})
    (q : H ⧸ N.subgroupOf H) :
    (N.localQuotientSplittingEquiv H hNH).symm K q =
      K.property.isComplement'_subgroupOf.quotientSplitting q := (rfl)

/-- The splitting attached to a local complement has exactly that complement as its ambient
range. -/
@[simp]
theorem map_range_localQuotientSplittingEquiv_symm (hNH : N ≤ H)
    (K : {K : Subgroup G // N.IsLocalComplement K H}) :
    ((N.localQuotientSplittingEquiv H hNH).symm K).toMonoidHom.range.map H.subtype = K.val :=
  congrArg Subtype.val ((N.localQuotientSplittingEquiv H hNH).apply_symm_apply K)

/-- A local complement exists precisely when the quotient extension inside `H` splits. -/
theorem exists_isLocalComplement_iff_nonempty_splitting_quotientExtension (hNH : N ≤ H) :
    (∃ K : Subgroup G, N.IsLocalComplement K H) ↔
      Nonempty (N.subgroupOf H).quotientExtension.Splitting := by
  rw [← nonempty_subtype]
  exact (N.localQuotientSplittingEquiv H hNH).nonempty_congr.symm

variable {N H} {K : Subgroup G}

namespace IsLocalComplement

variable (h : N.IsLocalComplement K H)

/-- The splitting of a local complement evaluates on each coset to the right component of
its product decomposition. -/
theorem coe_localQuotientSplittingEquiv_symm_mk (x : H) :
    ((N.localQuotientSplittingEquiv H h.left_le).symm ⟨K, h⟩
      (QuotientGroup.mk' (N.subgroupOf H) x) : G) = h.rightProjection x := by
  have hq : QuotientGroup.mk' (N.subgroupOf H) x =
      QuotientGroup.mk' (N.subgroupOf H)
        ⟨h.rightProjection x, h.right_le (h.rightProjection x).property⟩ := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    have he : (x : G) * (h.rightProjection x : G)⁻¹ = h.leftProjection x :=
      (eq_mul_inv_iff_mul_eq.mpr (h.leftProjection_mul_rightProjection x)).symm
    simpa only [mem_subgroupOf, div_eq_mul_inv, coe_mul, coe_inv, he] using
      (h.leftProjection x).property
  rw [hq, localQuotientSplittingEquiv_symm_apply]
  exact congrArg (fun y : H => (y : G))
    (h.isComplement'_subgroupOf.quotientSplitting_mk
      ⟨⟨h.rightProjection x, h.right_le (h.rightProjection x).property⟩,
        (h.rightProjection x).property⟩)

/-- The normal component is the remainder after removing the splitting value. -/
theorem coe_leftProjection_eq_mul_inv_localQuotientSplitting (x : H) :
    (h.leftProjection x : G) = (x : G) *
      ((N.localQuotientSplittingEquiv H h.left_le).symm ⟨K, h⟩
        (QuotientGroup.mk' (N.subgroupOf H) x) : G)⁻¹ := by
  rw [h.coe_localQuotientSplittingEquiv_symm_mk]
  exact eq_mul_inv_iff_mul_eq.mpr (h.leftProjection_mul_rightProjection x)

end IsLocalComplement

end Subgroup
