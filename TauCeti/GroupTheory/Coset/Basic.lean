/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

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
* `QuotientGroup.quotientRightRelEquivQuotientLeftRel_mk` and
  `QuotientGroup.quotientRightRelEquivQuotientLeftRel_symm_mk`: the right-to-left-coset
  equivalence sends the right coset of `x` to the left coset of `x⁻¹`, and back.

All of these have additive versions. The tower-coordinate reconstruction rules retain the inverse
laws after the coordinate maps themselves have been evaluated on quotients. Finally,
`Subgroup.sum_out_smul_eq_relIndex_nsmul` sums an orbit map along a tower: for `K ≤ H` and an
element `m` of an additive commutative monoid on which `G` acts, fixed by `H`, the sum of
`q.out • m` over the cosets of `K` is `[H : K]` times the sum over the cosets of `H`.
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

section QuotientTower

variable {G : Type*} [Group G] {U V : Subgroup G} (hVU : V ≤ U)
  (f : G ⧸ U → G) (hf : Function.RightInverse f QuotientGroup.mk)

/-- Reassemble the two tower coordinates after evaluating the inverse quotient map.

The before-simp rule preserves the coordinate inverse law before the coordinates themselves
expand to quotient maps. -/
@[simp↓] theorem quotientEquivProdOfLE'_reconstruct (q : G ⧸ V) :
    Quotient.map' (fun b : U ↦ f (quotientEquivProdOfLE' hVU f hf q).1 * b)
      (fun b c h ↦ by
        rw [QuotientGroup.leftRel_apply] at h ⊢
        rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left])
      (quotientEquivProdOfLE' hVU f hf q).2 = q := by
  simpa only [quotientEquivProdOfLE'_symm_apply] using
    (quotientEquivProdOfLE' hVU f hf).symm_apply_apply q

/-- The evaluated first coordinate of the inverse tower map is its outer coset. -/
@[simp↓] theorem quotientEquivProdOfLE'_map_fst_symm (a : G ⧸ U) (b : U ⧸ V.subgroupOf U) :
    Quotient.map' id (fun _ _ h ↦ QuotientGroup.leftRel_apply.mpr
        (hVU (QuotientGroup.leftRel_apply.mp h)))
      ((quotientEquivProdOfLE' hVU f hf).symm (a, b)) = a := by
  simpa only [quotientEquivProdOfLE'_apply] using
    congrArg Prod.fst ((quotientEquivProdOfLE' hVU f hf).apply_symm_apply (a, b))

/-- The evaluated second coordinate of the inverse tower map is its inner coset. -/
@[simp↓] theorem quotientEquivProdOfLE'_map_snd_symm (a : G ⧸ U) (b : U ⧸ V.subgroupOf U) :
    Quotient.map' (fun g : G ↦
      (⟨(f (Quotient.mk'' g))⁻¹ * g,
        QuotientGroup.leftRel_apply.mp (Quotient.exact' (hf g))⟩ : U))
      (fun b c h ↦ by
        rw [QuotientGroup.leftRel_apply]
        -- Compare the subgroup-of relation in the ambient group before using `hVU`.
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) ∈ V
        have key : f b = f c :=
          congrArg f (Quotient.sound'
            (QuotientGroup.leftRel_apply.mpr (hVU (QuotientGroup.leftRel_apply.mp h))))
        rwa [key, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left,
          ← QuotientGroup.leftRel_apply])
      ((quotientEquivProdOfLE' hVU f hf).symm (a, b)) = b := by
  simpa only [quotientEquivProdOfLE'_apply] using
    congrArg Prod.snd ((quotientEquivProdOfLE' hVU f hf).apply_symm_apply (a, b))

end QuotientTower

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

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
/-- **Summing an `H`-invariant orbit map along a tower.** For subgroups `K ≤ H` of finite index in
`G` and an element `m` of an additive commutative monoid on which `G` acts that is fixed by `H`,
the sum of `q.out • m` over the cosets of `K` is `[H : K]` times the sum over the cosets of
`H`: each coset of `H` is the union of `[H : K]` cosets of `K`, and `q.out • m` depends only on the
coset of `H` containing `q.out`. The action need only respect multiplication in `G`; it need not
preserve addition or zero in the monoid. -/
theorem sum_out_smul_eq_relIndex_nsmul {G : Type*} [Group G] {H K : Subgroup G} [K.FiniteIndex]
    [H.FiniteIndex] (hKH : K ≤ H) {M : Type*} [AddCommMonoid M] [SemigroupAction G M] {m : M}
    (hm : ∀ h ∈ H, h • m = m) :
    ∑ q : G ⧸ K, q.out • m = K.relIndex H • ∑ q : G ⧸ H, q.out • m := by
  classical
  -- Re-index the sum over `G ⧸ K` by the tower transversal `(p, k) ↦ p.out * k.out`.
  rw [← (mk_out_mul_out_bijective hKH).sum_comp (fun q : G ⧸ K ↦ q.out • m), Fintype.sum_prod_type]
  -- Each summand equals `p.out • m`, since `k.out ∈ H` and the representative of the coset of
  -- `p.out * k.out` differs from it by an element of `K ≤ H`.
  have key : ∀ (p : G ⧸ H) (k : H ⧸ K.subgroupOf H),
      ((p.out * (k.out : G) : G) : G ⧸ K).out • m = p.out • m := by
    intro p k
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul K (p.out * (k.out : G))
    rw [hz, mul_smul, mul_smul, hm _ (hKH z.2), hm _ k.out.2]
  simp only [key, Finset.sum_const, Finset.card_univ, Finset.sum_nsmul, relIndex, index_eq_card,
    Nat.card_eq_fintype_card]

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

/-- The right-to-left-coset equivalence sends the right coset of `x` to the left coset of
`x⁻¹`. -/
@[to_additive (attr := simp) /-- The right-to-left-coset equivalence sends the right coset of `x`
to the left coset of `-x`. -/]
theorem quotientRightRelEquivQuotientLeftRel_mk (x : G) :
    quotientRightRelEquivQuotientLeftRel H (Quotient.mk'' x) = (x⁻¹ : G) :=
  rfl

/-- The right-to-left-coset equivalence sends a right coset to the left coset of the inverse
of its chosen representative. -/
@[to_additive /-- The right-to-left-coset equivalence sends a right coset to the left coset of
the negative of its chosen representative. -/]
theorem quotientRightRelEquivQuotientLeftRel_apply (q : Quotient (rightRel H)) :
    quotientRightRelEquivQuotientLeftRel H q = (q.out⁻¹ : G) := by
  rw [← quotientRightRelEquivQuotientLeftRel_mk, Quotient.out_eq']

/-- The inverse of the right-to-left-coset equivalence sends the left coset of `x` to the right
coset of `x⁻¹`. -/
@[to_additive (attr := simp) /-- The inverse of the right-to-left-coset equivalence sends the left
coset of `x` to the right coset of `-x`. -/]
theorem quotientRightRelEquivQuotientLeftRel_symm_mk (x : G) :
    (quotientRightRelEquivQuotientLeftRel H).symm (x : G ⧸ H) = Quotient.mk'' x⁻¹ :=
  rfl

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
