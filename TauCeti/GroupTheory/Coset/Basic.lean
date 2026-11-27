/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
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
* `QuotientGroup.apply_out_mk`: a function invariant under right multiplication by `H` takes the
  same value at `g` and at the chosen representative of `g H`, and
  `QuotientGroup.finite_support_comp_inv_mul`: a left translate of such a function supported on
  finitely many cosets is again supported on finitely many cosets.
* `QuotientGroup.mk_out_smul` and `QuotientGroup.mk_mul_out_smul`: the representative of a
  translated coset `g • q` lies in the coset of `g * q.out`, and `QuotientGroup.inv_smul_of_mk_eq`
  and `QuotientGroup.out_inv_smul`: the inverse of a representative of `q`, for instance
  `q.out⁻¹`, translates `q` to the base point; `QuotientGroup.smul_mk_one_eq_mk`: the orbit map
  of the base point is the projection `G → G ⧸ H`.
* `QuotientGroup.outCocycle`: the element `(g • q).out⁻¹ * g * q.out` of `H` relating the two, with
  the cocycle identity `QuotientGroup.outCocycle_mul`.
* `QuotientGroup.iUnion_out_smul_eq` and `QuotientGroup.pairwise_disjoint_out_smul`: for an
  action on a type `α` and `V : Set α` mapped onto itself by `H`, the translates `q.out • V`
  cover `⋃ g, g • V`, and they are pairwise disjoint when every `g ∉ H` moves `V` off itself.
* `QuotientGroup.quotientRightRelEquivQuotientLeftRel_mk` and
  `QuotientGroup.quotientRightRelEquivQuotientLeftRel_symm_mk`: the right-to-left-coset
  equivalence sends the right coset of `x` to the left coset of `x⁻¹`, and back.

All of these have additive versions. The tower-coordinate reconstruction rules retain the inverse
laws after the coordinate maps themselves have been evaluated on quotients. Finally,
`Subgroup.sum_out_smul_eq_relIndex_nsmul` sums an orbit map along a tower: for `K ≤ H` and an
element `m` of an additive commutative monoid on which `G` acts, fixed by `H`, the sum of
`q.out • m` over the cosets of `K` is `[H : K]` times the sum over the cosets of `H`.
`Subgroup.finite_image_mk_of_inv_mul_mem` passes finiteness of the image of a set in `G ⧸ K` to
`G ⧸ L` when congruence modulo `K` on the set implies congruence modulo `L`.
`Subgroup.card_fiber_quotientMapOfLE` counts every fibre of `G / H → G / K` as `[K : H]`, and
`Subgroup.sum_comp_quotientMapOfLE` sums a function on `G / K` along that map.
`Subgroup.index_eq_of_equiv`, `Subgroup.ne_zero_of_equiv`, and `Subgroup.finiteIndex_of_equiv`
read the index, nonemptiness of `Fin n`, and `FiniteIndex` off a coset bijection;
`Subgroup.finiteIndex_of_surjective` and `Subgroup.index_le_of_surjective` deduce `FiniteIndex`
and an index bound from a surjection from a finite type; and `Subgroup.quotientEquivFin` constructs
a coset bijection `G ⧸ H ≃ Fin n` from `H.index = n` when `n ≠ 0`.
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

/-- Each fibre of the map `G / H → G / K`, for `H ≤ K`, has cardinality `[K : H]`.
No finiteness or normality assumption on either subgroup is needed. -/
@[to_additive /-- Each fibre of the map `G / H → G / K`, for `H ≤ K`, has cardinality
`[K : H]`. No finiteness assumption on either additive subgroup is needed. -/]
theorem card_fiber_quotientMapOfLE {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (q : G ⧸ K) :
    Nat.card {p : G ⧸ H // quotientMapOfLE hHK p = q} = H.relIndex K := by
  let e := (quotientEquivProdOfLE hHK).subtypeEquiv
    (p := fun p ↦ quotientMapOfLE hHK p = q) (q := fun p ↦ p.1 = q)
    -- The first coordinate of the tower equivalence is the quotient map itself.
    (fun p ↦ Iff.rfl)
  rw [Nat.card_congr e,
    Nat.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd
      (β := K ⧸ H.subgroupOf K) (p := fun a ↦ a = q)),
    Nat.card_prod, Nat.card_unique, one_mul]
  -- Relative index is the cardinality of the quotient by the subgroup inside `K`.
  rfl

/-- **Summing along the quotient map of a tower.** For `H ≤ K`, a function on `G / K` summed
along `G / H → G / K` is `[K : H]` times its sum over `G / K`, since each fibre has `[K : H]`
points (`card_fiber_quotientMapOfLE`). -/
theorem sum_comp_quotientMapOfLE {G : Type*} [Group G] {H K : Subgroup G} [Fintype (G ⧸ H)]
    [Fintype (G ⧸ K)] (hHK : H ≤ K) {M : Type*} [AddCommMonoid M] (F : G ⧸ K → M) :
    ∑ q : G ⧸ H, F (quotientMapOfLE hHK q) = H.relIndex K • ∑ q : G ⧸ K, F q := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (quotientMapOfLE hHK), ← Finset.sum_nsmul]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.mp hp).2], Finset.sum_const,
    ← card_fiber_quotientMapOfLE hHK q, Nat.card_eq_fintype_card, Fintype.card_subtype]

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
    rw [hz, mul_smul, mul_smul, hm _ (hKH z.property), hm _ k.out.property]
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

section FiniteImage

variable {G : Type*} [Group G]

/-- Finiteness of a coset image passes to another quotient if congruence on the set modulo the
first subgroup implies congruence modulo the second: for a set `s` with finite image in `G ⧸ K`,
if any two elements of `s` congruent modulo `K` are congruent modulo `L`, then `s` has finite
image in `G ⧸ L`. No normality and no containment between `K` and `L` is needed. -/
theorem finite_image_mk_of_inv_mul_mem {K L : Subgroup G} {s : Set G}
    (hfin : (((↑) : G → G ⧸ K) '' s).Finite)
    (hcong : ∀ x ∈ s, ∀ y ∈ s, x⁻¹ * y ∈ K → x⁻¹ * y ∈ L) :
    (((↑) : G → G ⧸ L) '' s).Finite := by
  classical
  -- Send a coarse class to the fine class of a chosen representative from `s`.
  let f : G ⧸ K → G ⧸ L := fun q ↦
    if h : ∃ x ∈ s, (x : G ⧸ K) = q then ((h.choose : G) : G ⧸ L) else ((1 : G) : G ⧸ L)
  refine (hfin.image f).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(x : G ⧸ K), ⟨x, hx, rfl⟩, ?_⟩
  have h : ∃ y ∈ s, (y : G ⧸ K) = x := ⟨x, hx, rfl⟩
  obtain ⟨hy, hyx⟩ := h.choose_spec
  have hf : f (x : G ⧸ K) = ((h.choose : G) : G ⧸ L) := by simp only [f, h, ↓reduceDIte]
  rw [hf]
  exact QuotientGroup.eq.mpr (hcong _ hy x hx (QuotientGroup.eq.mp hyx))

end FiniteImage

/-- An equivalence `G ⧸ H ≃ Fin n` witnesses that `H` has index `n`. -/
@[to_additive /-- An equivalence `G ⧸ H ≃ Fin n` witnesses that `H` has index `n`. -/]
theorem index_eq_of_equiv {G : Type*} [Group G] (H : Subgroup G) {n : ℕ}
    (e : G ⧸ H ≃ Fin n) : H.index = n := by
  rw [index_eq_card, Nat.card_congr e, Nat.card_fin]

/-- Because `G ⧸ H` contains the identity coset, any equivalence `G ⧸ H ≃ Fin n` forces `n ≠ 0`. -/
@[to_additive /-- Because `G ⧸ H` contains the zero coset, any equivalence `G ⧸ H ≃ Fin n` forces
`n ≠ 0`. -/]
theorem ne_zero_of_equiv {G : Type*} [Group G] (H : Subgroup G) {n : ℕ}
    (e : G ⧸ H ≃ Fin n) : n ≠ 0 :=
  (e ((1 : G) : G ⧸ H)).pos.ne'

/-- A subgroup whose coset space is equivalent to a finite type has finite index. -/
@[to_additive /-- An additive subgroup whose coset space is equivalent to a finite type has finite
index. -/]
theorem finiteIndex_of_equiv {G β : Type*} [Group G] [Finite β] (H : Subgroup G)
    (e : G ⧸ H ≃ β) : H.FiniteIndex :=
  have : Finite (G ⧸ H) := Finite.of_equiv β e.symm
  H.finiteIndex_of_finite_quotient

/-- A subgroup whose coset space admits a surjection from a finite type has finite index. -/
@[to_additive /-- An additive subgroup whose coset space admits a surjection from a finite type
has finite index. -/]
theorem finiteIndex_of_surjective {G β : Type*} [Group G] [Finite β] (H : Subgroup G)
    {f : β → G ⧸ H} (hf : Function.Surjective f) : H.FiniteIndex :=
  have : Finite (G ⧸ H) := Finite.of_surjective f hf
  H.finiteIndex_of_finite_quotient

/-- A surjection from a finite type onto `G ⧸ H` bounds `H.index` by `Nat.card β`. -/
@[to_additive /-- A surjection from a finite type onto `G ⧸ H` bounds `H.index` by
`Nat.card β`. -/]
theorem index_le_of_surjective {G β : Type*} [Group G] [Finite β] (H : Subgroup G)
    {f : β → G ⧸ H} (hf : Function.Surjective f) : H.index ≤ Nat.card β := by
  rw [index_eq_card]
  exact Nat.card_le_card_of_surjective f hf

/-- An enumeration of the left cosets of a subgroup `H` of finite index `n ≠ 0`. -/
@[to_additive /-- An enumeration of the left cosets of an additive subgroup `H` of finite index
`n ≠ 0`. -/]
noncomputable def quotientEquivFin {G : Type*} [Group G] (H : Subgroup G) {n : ℕ} [NeZero n]
    (hH : H.index = n) : G ⧸ H ≃ Fin n :=
  have hcard : Nat.card (G ⧸ H) = n := H.index_eq_card.symm.trans hH
  have : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero (hcard ▸ NeZero.ne n)
  Finite.equivFinOfCardEq hcard

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

/-- A function invariant under right multiplication by `H` takes the same value at `g` and at the
chosen representative of the coset `g H`. -/
@[to_additive /-- A function invariant under right addition of `H` takes the same value at `g` and
at the chosen representative of the coset `g + H`. -/]
theorem apply_out_mk {X : Type*} {f : G → X} (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) (g : G) :
    f (g : G ⧸ H).out = f g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hf g h h.property]

/-- A left translate `g ↦ f (x⁻¹ g)` of a right `K`-invariant `f` supported on finitely many cosets
is again supported on finitely many cosets. -/
theorem finite_support_comp_inv_mul {A : Type*} [Zero A] {K : Subgroup G} {f : G → A}
    (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g)
    (hf_fin : (Function.support fun q : G ⧸ K ↦ f q.out).Finite) (x : G) :
    (Function.support fun q : G ⧸ K ↦ f (x⁻¹ * q.out)).Finite := by
  have h_value (q : G ⧸ K) : f (x⁻¹ * q.out) = f (x⁻¹ • q).out := by
    rw [← MulAction.Quotient.mk_smul_out, smul_eq_mul, QuotientGroup.apply_out_mk hf]
  refine (hf_fin.preimage (MulAction.injective x⁻¹).injOn).subset fun q hq ↦ ?_
  simpa [h_value] using hq

/-- The chosen representative of the translate `g • q` of a left coset `q` lies in the same coset
as `g` times the chosen representative of `q`. -/
@[to_additive]
theorem mk_out_smul (g : G) (q : G ⧸ H) : ((g • q).out : G ⧸ H) = (g * q.out : G) := by
  simp [← smul_eq_mul]

/-- The inverse of a representative `g` of a left coset `q` translates `q` to the base point
`⟦1⟧`. -/
@[to_additive /-- The negative of a representative `g` of a left coset `q` translates `q` to the
base point `⟦0⟧`. -/]
theorem inv_smul_of_mk_eq {g : G} {q : G ⧸ H} (h : (g : G ⧸ H) = q) :
    g⁻¹ • q = ((1 : G) : G ⧸ H) := by
  rw [← h, MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel]

/-- The inverse of the chosen representative of a left coset `q` translates `q` to the base point
`⟦1⟧`. -/
@[to_additive (attr := simp) /-- The negative of the chosen representative of a left coset `q`
translates `q` to the base point `⟦0⟧`. -/]
theorem out_inv_smul (q : G ⧸ H) : q.out⁻¹ • q = ((1 : G) : G ⧸ H) :=
  inv_smul_of_mk_eq (QuotientGroup.out_eq' q)

/-- The orbit map `g ↦ g • ⟦1⟧` of the base point of `G ⧸ H` is the projection `G → G ⧸ H`. -/
@[to_additive /-- The orbit map `g ↦ g +ᵥ ⟦0⟧` of the base point of `G ⧸ H` is the projection
`G → G ⧸ H`. -/]
theorem smul_mk_one_eq_mk : (fun g : G ↦ g • ((1 : G) : G ⧸ H)) = (QuotientGroup.mk : G → G ⧸ H) :=
  funext fun g ↦ by rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]

/-- For `h ∈ H` and a coset `k ∈ H ⧸ K.subgroupOf H`, the elements `a * (h • k).out` and
`a * h * k.out` of `G` lie in the same left coset of `K`, for every `a ∈ G`. No inclusion `K ≤ H`
is needed. -/
@[to_additive]
theorem mk_mul_out_smul {K : Subgroup G} (a : G) (h : H) (k : H ⧸ K.subgroupOf H) :
    ((a * (h • k).out : G) : G ⧸ K) = (a * h * k.out : G) := by
  -- `(h • k).out` and `h * k.out` differ by an element of `K.subgroupOf H`, i.e. of `K`.
  simpa [QuotientGroup.eq, Subgroup.mem_subgroupOf, mul_assoc] using
    QuotientGroup.eq.mp (mk_out_smul h k)

/-- The cocycle of the translation action of `G` on `G ⧸ H` relative to the chosen
representatives: the element `(g • q).out⁻¹ * g * q.out` of `H`, so that
`g * q.out = (g • q).out * outCocycle g q`. -/
@[to_additive /-- The cocycle of the translation action of `G` on `G ⧸ H` relative to the chosen
representatives: the element `-(g +ᵥ q).out + g + q.out` of `H`, so that
`g + q.out = (g +ᵥ q).out + outCocycle g q`. -/]
noncomputable def outCocycle (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * g * q.out, by simpa [mul_assoc] using QuotientGroup.eq.mp (mk_out_smul g q)⟩

@[to_additive (attr := simp)]
theorem coe_outCocycle (g : G) (q : G ⧸ H) :
    (outCocycle g q : G) = (g • q).out⁻¹ * g * q.out :=
  (rfl)

-- Not `@[simp]`: `coe_outCocycle` already rewrites the left-hand side.
/-- Translating a chosen representative by `g` gives the chosen representative of the translated
coset times the cocycle. -/
@[to_additive /-- Translating a chosen representative by `g` gives the chosen
representative of the translated coset plus the cocycle. -/]
theorem out_mul_outCocycle (g : G) (q : G ⧸ H) :
    (g • q).out * (outCocycle g q : G) = g * q.out := by
  simp [mul_assoc]

@[to_additive (attr := simp)]
theorem outCocycle_one (q : G ⧸ H) : outCocycle 1 q = 1 := by
  ext
  simp

/-- The cocycle identity. -/
@[to_additive /-- The cocycle identity. -/]
theorem outCocycle_mul (g h : G) (q : G ⧸ H) :
    outCocycle (g * h) q = outCocycle g (h • q) * outCocycle h q := by
  ext
  simp [mul_smul, mul_assoc]

section Action

open scoped Pointwise

variable {α : Type*} [MulAction G α] {V : Set α}

/-- The translates of `V` by the chosen coset representatives cover `⋃ g, g • V`, when `H` maps
`V` onto itself. -/
@[to_additive /-- The translates of `V` by the chosen coset representatives cover
`⋃ g, g +ᵥ V`, when `H` maps `V` onto itself. -/]
theorem iUnion_out_smul_eq (hH : ∀ h ∈ H, h • V = V) :
    ⋃ q : G ⧸ H, (q.out : G) • V = ⋃ g : G, g • V := by
  refine Set.Subset.antisymm
    (Set.iUnion_subset fun q => Set.subset_iUnion (fun g : G => g • V) _) ?_
  refine Set.iUnion_subset fun g => ?_
  obtain ⟨h, hh⟩ := mk_out_eq_mul H g
  -- `g = out * h⁻¹`, and `h⁻¹` maps `V` onto itself.
  have hg : g • V = ((g : G ⧸ H).out : G) • V := by
    rw [hh, mul_smul, hH _ h.property]
  exact hg ▸ Set.subset_iUnion (fun q : G ⧸ H => (q.out : G) • V) _

/-- Translates of `V` by distinct chosen coset representatives are disjoint, when every `g ∉ H`
moves `V` off itself. -/
@[to_additive /-- Translates of `V` by distinct chosen coset representatives are disjoint, when
every `g ∉ H` moves `V` off itself. -/]
theorem pairwise_disjoint_out_smul (hdisj : ∀ g ∉ H, Disjoint (g • V) V) :
    Pairwise (Function.onFun Disjoint fun q : G ⧸ H => (q.out : G) • V) := by
  intro q q' hqq'
  have hmem : ((q'.out : G))⁻¹ * q.out ∉ H := fun hm => by
    have h := (QuotientGroup.eq (s := H) (a := q'.out) (b := q.out)).2 hm
    rw [out_eq', out_eq'] at h
    exact hqq' h.symm
  have := (Set.disjoint_smul_set (a := (q'.out : G))).2 (hdisj _ hmem)
  rwa [smul_smul, mul_inv_cancel_left] at this

end Action

/-- Reindex a `finsum` over `G ⧸ K` along left multiplication by `a : G` when the summand is
right `K`-invariant. -/
theorem finsum_mulLeft_eq {G M : Type*} [Group G] [AddCommMonoid M] {K : Subgroup G}
    (a : G) (F : G → M) (hF : ∀ g : G, ∀ k ∈ K, F (g * k) = F g) :
    (∑ᶠ q : G ⧸ K, F (a * q.out)) = ∑ᶠ q : G ⧸ K, F q.out := by
  refine (finsum_congr fun q ↦ ?_).trans (finsum_comp_equiv (MulAction.toPerm a))
  have hk : (a * q.out)⁻¹ * (a • q).out ∈ K :=
    QuotientGroup.eq.1 (mk_out_smul a q).symm
  have heq : (a • q).out = a * q.out * ((a * q.out)⁻¹ * (a • q).out) := by
    rw [mul_inv_cancel_left]
  rw [MulAction.toPerm_apply, heq, hF _ _ hk]

end QuotientGroup

namespace Subgroup

/-- If a monoid homomorphism `τ : G →* G` sends every `g⁻¹` into the double coset `K * g * K`,
then `τ` preserves `K`. -/
theorem map_mem_iff_of_inv_mem_doubleCoset {G F : Type*} [Group G] {K : Subgroup G}
    [FunLike F G G] [MonoidHomClass F G G] {τ : F}
    (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) (g : G) :
    τ g ∈ K ↔ g ∈ K := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hg⟩ := hτg g
    have hτinv : τ g⁻¹ ∈ K := by simpa [map_inv] using K.inv_mem h
    have heq : g = a⁻¹ * τ g⁻¹ * b⁻¹ := by simp [hg, mul_assoc]
    rw [heq]
    exact K.mul_mem (K.mul_mem (K.inv_mem ha) hτinv) (K.inv_mem hb)
  · intro h
    obtain ⟨a, ha, b, hb, hg⟩ := hτg g⁻¹
    rw [inv_inv] at hg
    rw [hg]
    exact K.mul_mem (K.mul_mem ha (K.inv_mem h)) hb

/-- The equivalence on left cosets `G ⧸ K ≃ G ⧸ K` induced by a group automorphism `τ : G ≃* G`
sending every `g⁻¹` into the double coset `K * g * K`. -/
noncomputable def quotientEquivOfInvMemDoubleCoset {G : Type*} [Group G] (K : Subgroup G)
    (τ : G ≃* G) (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) : G ⧸ K ≃ G ⧸ K :=
  Equiv.ofBijective _
    (mk_mulEquiv_out_bijective τ (K.map_mem_iff_of_inv_mem_doubleCoset hτg))

/-- Application formula for `Subgroup.quotientEquivOfInvMemDoubleCoset`. -/
theorem quotientEquivOfInvMemDoubleCoset_apply {G : Type*} [Group G] (K : Subgroup G)
    (τ : G ≃* G) (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) (q : G ⧸ K) :
    K.quotientEquivOfInvMemDoubleCoset τ hτg q = ((τ q.out : G) : G ⧸ K) :=
  (rfl)

/-- `Subgroup.quotientEquivOfInvMemDoubleCoset` sends the coset of `g` to the coset of `τ g`. -/
@[simp] theorem quotientEquivOfInvMemDoubleCoset_mk {G : Type*} [Group G] (K : Subgroup G)
    (τ : G ≃* G) (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) (g : G) :
    K.quotientEquivOfInvMemDoubleCoset τ hτg (g : G ⧸ K) = ((τ g : G) : G ⧸ K) := by
  rw [quotientEquivOfInvMemDoubleCoset_apply, QuotientGroup.eq, ← map_inv, ← map_mul,
    K.map_mem_iff_of_inv_mem_doubleCoset hτg, ← QuotientGroup.eq, QuotientGroup.out_eq']

/-- The inverse of `Subgroup.quotientEquivOfInvMemDoubleCoset` sends the coset of `g` to the coset
of `τ.symm g`. -/
@[simp] theorem quotientEquivOfInvMemDoubleCoset_symm_mk {G : Type*} [Group G] (K : Subgroup G)
    (τ : G ≃* G) (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) (g : G) :
    (K.quotientEquivOfInvMemDoubleCoset τ hτg).symm (g : G ⧸ K) = ((τ.symm g : G) : G ⧸ K) := by
  apply (K.quotientEquivOfInvMemDoubleCoset τ hτg).injective
  simp

/-- The chosen representative of `K.quotientEquivOfInvMemDoubleCoset τ hτg q` differs from
`τ q.out` on the right by an element of `K`. -/
theorem out_quotientEquivOfInvMemDoubleCoset_eq_mul {G : Type*} [Group G] (K : Subgroup G)
    (τ : G ≃* G) (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) (q : G ⧸ K) :
    ∃ k ∈ K, (K.quotientEquivOfInvMemDoubleCoset τ hτg q).out = τ q.out * k := by
  obtain ⟨⟨k, hk⟩, hq⟩ := QuotientGroup.mk_out_eq_mul K (τ q.out)
  exact ⟨k, hk, by rw [quotientEquivOfInvMemDoubleCoset_apply]; exact hq⟩

end Subgroup
