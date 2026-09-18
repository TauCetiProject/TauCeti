/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Coset.Basic

/-!
# Evaluating the decomposition of a group into cosets and a subgroup

For a subgroup `s` of a group `α`, Mathlib's `Subgroup.groupEquivQuotientProdSubgroup` identifies
`α` with `(α ⧸ s) × s`, using the chosen representatives `Quotient.out` of the left cosets. It is
built as a composite of equivalences through a `Sigma` type, one step of which is a cast along the
equality of a coset with the fibre of the quotient map, so its values are not available by
unfolding. This file records them:

* `Subgroup.groupEquivQuotientProdSubgroup_symm_apply`: the pair `(q, x)` goes to `q.out * x`;
* `Subgroup.groupEquivQuotientProdSubgroup_apply`: an element `g` goes to its coset `⟦g⟧` and the
  element `⟦g⟧.out⁻¹ * g` of `s`, with the projections `groupEquivQuotientProdSubgroup_apply_fst`
  and `groupEquivQuotientProdSubgroup_apply_snd_coe`.

The additive versions are generated for `AddSubgroup.addGroupEquivQuotientProdAddSubgroup`.

For subgroups `K ≤ L`, the cosets of `H` in `K` may be formed either in `K` itself or after
passing to the copies of `H` and `K` inside `L`:

* `Subgroup.quotientSubgroupOfSubgroupOfEquiv`: the two coset spaces are equivalent, with value
  `Subgroup.quotientSubgroupOfSubgroupOfEquiv_apply_mk` on a coset.
-/

public section

namespace Subgroup

/-- An equivalence obtained by casting the identity of a subtype along an equality of subtypes of
the same type does not move underlying elements. -/
private theorem coe_cast_refl_symm_apply {α : Type*} {p r : α → Prop} (hpr : p = r)
    (H : ({x // p x} ≃ {x // p x}) = ({x // p x} ≃ {x // r x})) (y : {x // r x}) :
    (((cast H (Equiv.refl _)).symm y : {x // p x}) : α) = y := by
  subst hpr
  rw [cast_eq]
  rfl

variable {α : Type*} [Group α] {s : Subgroup α}

/-- **The decomposition of a group into cosets and a subgroup, read backwards:** the pair of a
left coset `q` and an element `x` of the subgroup is the element `q.out * x`. -/
@[to_additive (attr := simp)]
theorem groupEquivQuotientProdSubgroup_symm_apply (q : α ⧸ s) (x : s) :
    groupEquivQuotientProdSubgroup.symm (q, x) = q.out * x := by
  simp only [groupEquivQuotientProdSubgroup, Equiv.trans_def, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.sigmaFiberEquiv_apply, Equiv.sigmaEquivProd_symm_apply,
    Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, eq_mpr_eq_cast, id_eq, cast_cast]
  -- The middle step is the identity of the fibre over `q`, cast to the coset `q.out • s`.
  refine (coe_cast_refl_symm_apply (funext fun y ↦ ?_) _ _).trans (rfl)
  rw [← QuotientGroup.eq_class_eq_leftCoset, Set.mem_ofPred_eq, QuotientGroup.out_eq']

/-- **The decomposition of a group into cosets and a subgroup:** an element `g` goes to its left
coset `⟦g⟧` and the element `⟦g⟧.out⁻¹ * g` of the subgroup. -/
@[to_additive]
theorem groupEquivQuotientProdSubgroup_apply (g : α) :
    groupEquivQuotientProdSubgroup g =
      ((g : α ⧸ s), ⟨(g : α ⧸ s).out⁻¹ * g, QuotientGroup.leftRel_apply.1
        (Quotient.exact' (QuotientGroup.out_eq' (g : α ⧸ s)))⟩) := by
  refine groupEquivQuotientProdSubgroup.symm.injective ?_
  rw [Equiv.symm_apply_apply, groupEquivQuotientProdSubgroup_symm_apply, mul_inv_cancel_left]

/-- The coset component of the decomposition of `g` is the coset of `g`. -/
@[to_additive (attr := simp)]
theorem groupEquivQuotientProdSubgroup_apply_fst (g : α) :
    (groupEquivQuotientProdSubgroup (s := s) g).1 = (g : α ⧸ s) := by
  rw [groupEquivQuotientProdSubgroup_apply]

/-- The subgroup component of the decomposition of `g` is `⟦g⟧.out⁻¹ * g`. -/
@[to_additive (attr := simp)]
theorem groupEquivQuotientProdSubgroup_apply_snd_coe (g : α) :
    ((groupEquivQuotientProdSubgroup (s := s) g).2 : α) = (g : α ⧸ s).out⁻¹ * g := by
  rw [groupEquivQuotientProdSubgroup_apply]

/-- **Cosets of `H` in `K`, read inside an ambient `L ≥ K`.** For `K ≤ L`, the cosets of the copy of
`H` in the copy of `K` inside `L` are the cosets of `H` in `K`, along
`Subgroup.subgroupOfEquivOfLe`. -/
@[expose, to_additive /-- **Cosets of `H` in `K`, read inside an ambient `L ≥ K`.** For `K ≤ L`, the
cosets of the copy of `H` in the copy of `K` inside `L` are the cosets of `H` in `K`, along
`AddSubgroup.addSubgroupOfEquivOfLe`. -/]
def quotientSubgroupOfSubgroupOfEquiv {H K L : Subgroup α} (hKL : K ≤ L) :
    K.subgroupOf L ⧸ (H.subgroupOf L).subgroupOf (K.subgroupOf L) ≃ K ⧸ H.subgroupOf K :=
  Quotient.congr (subgroupOfEquivOfLe hKL).toEquiv fun x y ↦ by
    simp [QuotientGroup.leftRel_apply, mem_subgroupOf]

/-- The equivalence `Subgroup.quotientSubgroupOfSubgroupOfEquiv` sends the coset of `g` to the
coset of the same element of `K`. -/
@[to_additive (attr := simp)]
theorem quotientSubgroupOfSubgroupOfEquiv_apply_mk {H K L : Subgroup α} (hKL : K ≤ L)
    (g : K.subgroupOf L) :
    quotientSubgroupOfSubgroupOfEquiv (H := H) hKL (g : K.subgroupOf L ⧸ _) =
      (subgroupOfEquivOfLe hKL g : K ⧸ H.subgroupOf K) :=
  rfl

end Subgroup
