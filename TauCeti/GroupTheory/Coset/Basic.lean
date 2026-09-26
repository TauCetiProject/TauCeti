/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

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

The file also records how the chosen representatives behave along a tower of subgroups, along an
isomorphism of groups, and under translation:

* `Subgroup.mk_out_mul_out_bijective`: for `K ≤ H`, the products `p.out * k.out` of chosen
  representatives of `G ⧸ H` and of `H ⧸ K.subgroupOf H` form a transversal of `K` in `G`;
* `Subgroup.mk_mulEquiv_out_bijective`: an isomorphism `e : G ≃* G'` carrying `H` onto `H'` carries
  the chosen representatives of `G ⧸ H` to a transversal of `H'` in `G'`;
* `QuotientGroup.mk_out_smul` and `QuotientGroup.mk_mul_out_smul`: the representative of a
  translated coset `g • q` lies in the coset of `g * q.out`.

All of these have additive versions.
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

/-- **Transversals multiply along a tower.** For subgroups `K ≤ H` of `G`, the products
`p.out * k.out` of the chosen representatives of the cosets `p ∈ G ⧸ H` and
`k ∈ H ⧸ K.subgroupOf H` represent each coset of `K` in `G` exactly once. -/
@[to_additive]
theorem mk_out_mul_out_bijective {G : Type*} [Group G] {H K : Subgroup G} (hKH : K ≤ H) :
    Function.Bijective
      fun i : (G ⧸ H) × (H ⧸ K.subgroupOf H) ↦ ((i.1.out * (i.2.out : G) : G) : G ⧸ K) := by
  convert (quotientEquivProdOfLE hKH).symm.bijective with ⟨p, k⟩
  -- The inverse of `quotientEquivProdOfLE` sends `(p, ⟦k.out⟧)` to `⟦p.out * k.out⟧`.
  conv_rhs => rw [quotientEquivProdOfLE_symm_apply, ← QuotientGroup.out_eq' k, Quotient.map'_mk'']

/-- **An isomorphism carries a transversal to a transversal.** If `e : G ≃* G'` carries `H`
onto `H'`, then the images under `e` of the chosen representatives of the cosets of `H` represent
each coset of `H'` exactly once. Neither subgroup need be normal. -/
@[to_additive]
theorem mk_mulEquiv_out_bijective {G G' : Type*} [Group G] [Group G'] {H : Subgroup G}
    {H' : Subgroup G'} (e : G ≃* G') (he : ∀ g, e g ∈ H' ↔ g ∈ H) :
    Function.Bijective fun q : G ⧸ H ↦ ((e q.out : G') : G' ⧸ H') := by
  -- `e` carries "same left coset of `H`" to "same left coset of `H'`".
  have hmk : ∀ a b : G, ((e a : G') : G' ⧸ H') = e b ↔ (a : G ⧸ H) = b := by
    simp [QuotientGroup.eq, ← he]
  exact ⟨fun q q' h ↦ by simpa using (hmk _ _).1 h,
    fun q' ↦ ⟨e.symm q'.out, by simpa using (hmk _ (e.symm q'.out)).2 (QuotientGroup.out_eq' _)⟩⟩

end Subgroup

namespace QuotientGroup

variable {G : Type*} [Group G] {H : Subgroup G}

/-- The chosen representative of the translate `g • q` of a left coset `q` lies in the same coset
as `g` times the chosen representative of `q`. -/
@[to_additive]
theorem mk_out_smul (g : G) (q : G ⧸ H) : ((g • q).out : G ⧸ H) = (g * q.out : G) := by
  simp [← smul_eq_mul]

/-- For `h ∈ H` and a coset `k ∈ H ⧸ K.subgroupOf H`, the elements `a * (h • k).out` and
`a * h * k.out` of `G` lie in the same left coset of `K`, for every `a ∈ G`. No inclusion `K ≤ H`
is needed. -/
@[to_additive]
theorem mk_mul_out_smul {K : Subgroup G} (a : G) (h : H) (k : H ⧸ K.subgroupOf H) :
    ((a * (h • k).out : G) : G ⧸ K) = (a * h * k.out : G) := by
  -- `(h • k).out` and `h * k.out` differ by an element of `K.subgroupOf H`, i.e. of `K`.
  simpa [QuotientGroup.eq, Subgroup.mem_subgroupOf, mul_assoc] using
    QuotientGroup.eq.mp (mk_out_smul h k)

end QuotientGroup
