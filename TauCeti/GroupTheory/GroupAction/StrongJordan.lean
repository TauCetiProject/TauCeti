/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Strong Jordan criteria for normal subgroups

The fixing-subgroup criteria for double transitivity and double primitivity also apply
to a normal subgroup of a preprimitive action. In particular, the normal closure of
the fixing subgroup satisfies the stronger forms of Wielandt's criteria 13.1'.
-/

public section

open MulAction SubMulAction Subgroup MulAction.IsPreprimitive

open scoped Pointwise

variable {G α : Type*} [Group G] [MulAction G α]

/-- Jordan's criteria for 2-pretransitivity and 2-preprimitivity, for a normal subgroup:
let `G` act preprimitively on a finite type `α`, let `N` be a normal subgroup of `G`,
and let `s` be a nonempty subset of `α` whose complement has at least two points.
If `fixingSubgroup N s` acts transitively (resp. preprimitively) on the complement of `s`,
then `N` acts 2-pretransitively (resp. 2-preprimitively). -/
theorem MulAction.IsPreprimitive.is_two_motive_of_normal
    (hG : IsPreprimitive G α) {N : Subgroup G} [hN : N.Normal] {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) :
    (IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s) →
      IsMultiplyPretransitive N α 2) ∧
    (IsPreprimitive (fixingSubgroup N s) (ofFixingSubgroup N s) →
      IsMultiplyPreprimitive N α 2) := by
  have : Finite α := Nat.finite_of_card_ne_zero (by omega)
  induction n using Nat.strong_induction_on generalizing s with | _ n hrec
  have hsc : 1 < sᶜ.ncard := by
    have := Set.ncard_add_ncard_compl s
    omega
  rcases n with _ | n
  · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp hsn
    suffices IsPretransitive (fixingSubgroup N {a}) (ofFixingSubgroup N {a}) →
        IsPretransitive N α by
      refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
      · have := this hs
        rw [ofStabilizer.isMultiplyPretransitive (a := a), is_one_pretransitive_iff]
        exact .of_surjective_map ofFixingSubgroup_of_singleton_bijective.surjective hs
      · have := this hs.toIsPretransitive
        rw [isMultiplyPreprimitive_succ_iff_ofStabilizer N α le_rfl (a := a),
          is_one_preprimitive_iff]
        exact .of_surjective ofFixingSubgroup_of_singleton_bijective.surjective
    intro hs
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.one_lt_ncard_iff_nontrivial.mp hsc
    obtain ⟨k, hk⟩ := exists_smul_eq (fixingSubgroup N {a})
      (⟨x, hx⟩ : ofFixingSubgroup N {a}) ⟨y, hy⟩
    exact IsQuasiPreprimitive.isPretransitive_of_normal fun h ↦
      hxy <| (Set.eq_univ_iff_forall.mp h x k).symm.trans (congrArg Subtype.val hk)
  obtain ⟨g, hlt, hne, hu⟩ : ∃ g : G, (s ∩ g • s).ncard < s.ncard ∧ (s ∩ g • s).Nonempty ∧
      s ∪ g • s ≠ .univ := by
    rcases Nat.lt_or_ge (2 * s.ncard) (Nat.card α) with h | h
    · obtain ⟨a, ha, b, hb, hab⟩ := Set.one_lt_ncard_iff_nontrivial.mp (by omega : 1 < s.ncard)
      obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_notMem_smul (G := G) s.toFinite ⟨a, ha⟩
        (fun h ↦ by simp [h] at hsc) hab
      refine ⟨g, Set.ncard_lt_ncard ⟨Set.inter_subset_left, fun h ↦ hgb (h hb).2⟩,
        ⟨a, ha, hga⟩, Set.union_ne_univ_of_ncard_add_ncard_lt ?_⟩
      rwa [Set.ncard_smul_set, ← two_mul]
    · obtain ⟨a, ha, b, hb, hab⟩ := Set.one_lt_ncard_iff_nontrivial.mp hsc
      obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_notMem_smul (G := G) sᶜ.toFinite ⟨a, ha⟩
        (Set.compl_ne_univ.mpr (Set.nonempty_of_ncard_ne_zero (by omega))) hab
      simp only [Set.smul_set_compl, Set.mem_compl_iff, not_not] at hga hgb
      have hu : s ∪ g • s ≠ .univ := fun h ↦ (h ▸ Set.mem_univ a).elim ha hga
      refine ⟨g, (Set.ncard_lt_ncard ⟨Set.inter_subset_right, fun h ↦ hb (h hgb).1⟩).trans_eq
        (Set.ncard_smul_set g s), Set.nonempty_inter_of_le_ncard_add_ncard ?_ hu, hu⟩
      rwa [Set.ncard_smul_set, ← two_mul]
  obtain ⟨c, hc⟩ : ∃ c, c ∉ s ∧ c ∉ g • s := by simpa [Set.eq_univ_iff_forall] using hu
  have key (hs : IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s)) :
      IsPretransitive (fixingSubgroup N (s ∩ g • s)) (ofFixingSubgroup N (s ∩ g • s)) := by
    rw [isPretransitive_iff_base (⟨c, fun h ↦ hc.1 h.1⟩ : ofFixingSubgroup N (s ∩ g • s))]
    rintro ⟨x, hx⟩
    rcases not_and_or.mp hx with hxs | hxs
    · obtain ⟨⟨k, hk⟩, hkx⟩ := exists_smul_eq (fixingSubgroup N s)
        (⟨c, hc.1⟩ : ofFixingSubgroup N s) ⟨x, hxs⟩
      exact ⟨⟨k, fixingSubgroup_antitone N α Set.inter_subset_left hk⟩,
        Subtype.ext (congrArg Subtype.val hkx :)⟩
    · rw [Set.mem_smul_set_iff_inv_smul_mem] at hxs hc
      obtain ⟨⟨k, hk⟩, hkx⟩ := exists_smul_eq (fixingSubgroup N s)
        (⟨g⁻¹ • c, hc.2⟩ : ofFixingSubgroup N s) ⟨g⁻¹ • x, hxs⟩
      rw [mem_fixingSubgroup_iff] at hk
      refine ⟨⟨⟨g * k * g⁻¹, hN.conj_mem k k.prop g⟩, (mem_fixingSubgroup_iff N).mpr
        fun y hy ↦ ?_⟩, Subtype.ext ?_⟩
      · simpa [mul_smul, Subgroup.smul_def, smul_eq_iff_eq_inv_smul] using
          hk _ (Set.mem_smul_set_iff_inv_smul_mem.mp hy.2)
      · simpa [mul_smul, eq_inv_smul_iff, Subgroup.smul_def] using congrArg Subtype.val hkx
  have hpos := (Set.ncard_pos (s := s ∩ g • s)).mpr hne
  have h := hrec ((s ∩ g • s).ncard - 1) (by omega) (s := s ∩ g • s) (by omega) (by omega)
  refine ⟨fun hs ↦ h.1 (key hs), fun hs ↦ h.2 ?_⟩
  have := key hs.toIsPretransitive
  apply IsPreprimitive.of_card_lt (f := ofFixingSubgroup_of_inclusion N Set.inter_subset_left)
  rw [show Nat.card (ofFixingSubgroup N (s ∩ g • s)) = (s ∩ g • s)ᶜ.ncard from
    Nat.card_coe_set_eq _, Set.ncard_range_of_injective ofFixingSubgroup_of_inclusion_injective,
    show Nat.card (ofFixingSubgroup N s) = sᶜ.ncard from Nat.card_coe_set_eq _, Set.compl_inter]
  refine (Set.ncard_union_lt sᶜ.toFinite (g • s)ᶜ.toFinite ?_).trans_le ?_
  · rwa [Set.disjoint_compl_right_iff_subset, Set.compl_subset_iff_union]
  · rw [← Set.smul_set_compl, Set.ncard_smul_set, two_mul]

/-- Jordan's criterion `MulAction.IsPreprimitive.is_two_pretransitive` for a normal subgroup:
if `N` is a normal subgroup of `G` and `fixingSubgroup N s` acts transitively
on `ofFixingSubgroup N s`, then `N` acts 2-pretransitively. -/
theorem MulAction.IsPreprimitive.is_two_pretransitive_of_normal
    (hG : IsPreprimitive G α) {N : Subgroup G} [N.Normal] {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s)) :
    IsMultiplyPretransitive N α 2 :=
  (hG.is_two_motive_of_normal hsn hsn').1 hs_trans

/-- Jordan's criterion `MulAction.IsPreprimitive.is_two_preprimitive` for a normal subgroup:
if `N` is a normal subgroup of `G` and `fixingSubgroup N s` acts preprimitively
on `ofFixingSubgroup N s`, then `N` acts 2-preprimitively. -/
theorem MulAction.IsPreprimitive.is_two_preprimitive_of_normal
    (hG : IsPreprimitive G α) {N : Subgroup G} [N.Normal] {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup N s) (ofFixingSubgroup N s)) :
    IsMultiplyPreprimitive N α 2 :=
  (hG.is_two_motive_of_normal hsn hsn').2 hs_prim

/-- A stronger version of Jordan's criterion for 2-pretransitivity (Wielandt, 13.1'):
under the hypotheses of `MulAction.IsPreprimitive.is_two_pretransitive`,
the normal closure of `fixingSubgroup G s` acts 2-pretransitively. -/
theorem MulAction.IsPreprimitive.is_two_pretransitive'
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPretransitive (normalClosure (fixingSubgroup G s : Set G)) α 2 := by
  refine hG.is_two_pretransitive_of_normal hsn hsn' ⟨fun x y ↦ ?_⟩
  obtain ⟨⟨k, hk⟩, hkxy⟩ := exists_smul_eq (fixingSubgroup G s)
    (⟨x, x.prop⟩ : ofFixingSubgroup G s) ⟨y, y.prop⟩
  exact ⟨⟨⟨k, le_normalClosure hk⟩, hk⟩, Subtype.ext (congrArg Subtype.val hkxy :)⟩

/-- A stronger version of Jordan's criterion for 2-preprimitivity (Wielandt, 13.1'):
under the hypotheses of `MulAction.IsPreprimitive.is_two_preprimitive`,
the normal closure of `fixingSubgroup G s` acts 2-preprimitively. -/
theorem MulAction.IsPreprimitive.is_two_preprimitive_strong_jordan
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive (normalClosure (fixingSubgroup G s : Set G)) α 2 := by
  let N := normalClosure (fixingSubgroup G s : Set G)
  let f : ofFixingSubgroup G s →ₑ[fun k : fixingSubgroup G s ↦
      (⟨⟨k, le_normalClosure k.prop⟩, k.prop⟩ : fixingSubgroup N s)] ofFixingSubgroup N s :=
    { toFun x := ⟨x, x.prop⟩, map_smul' _ _ := rfl }
  exact hG.is_two_preprimitive_of_normal hsn hsn' <|
    IsPreprimitive.of_surjective (f := f) fun x ↦ ⟨⟨x, x.prop⟩, rfl⟩
