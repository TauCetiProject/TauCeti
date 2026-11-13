/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Semidirect products and multiplication of normalizing subgroups

Let `H` and `K` be subgroups of a group `G` with `K ≤ Subgroup.normalizer H`. Multiplication then
carries the external semidirect product `H ⋊ K` into `G` (`SemidirectProduct.monoidHomSubgroup`),
and its image is the join `H ⊔ K`. The corresponding elementwise normal form of `H ⊔ K` is
`Subgroup.mem_sup_of_right_le_normalizer_left` in `TauCeti.Algebra.Group.Subgroup.Pointwise`.
An invariant normal subgroup of the first factor is normal in the full semidirect product
(`Subgroup.normal_map_inl`).

## Main results

* `SemidirectProduct.lift_apply`: the external lift evaluates a pair by multiplying the
  images of its components.
* `SemidirectProduct.range_monoidHomSubgroup`: the range of the semidirect-product
  multiplication homomorphism is `H ⊔ K`.
* `SemidirectProduct.ker_rightHom_sup_range_inr`: the kernel of the projection to the acting group
  and the acting group generate the semidirect product.
* `SemidirectProduct.mem_ker_monoidHomSubgroup_iff`: its kernel consists of antidiagonal pairs.
* `SemidirectProduct.ker_monoidHomSubgroup_le_ker_lift_iff`: an external lift kills this kernel
  exactly when the two maps agree on the intersection.
* `SemidirectProduct.injective_monoidHomSubgroup_iff`,
  `SemidirectProduct.surjective_monoidHomSubgroup_iff`, and
  `SemidirectProduct.bijective_monoidHomSubgroup_iff`: injectivity, surjectivity, and bijectivity
  criteria for `SemidirectProduct.monoidHomSubgroup`.
* `SemidirectProduct.toEquiv_mulEquivSubgroup` and
  `SemidirectProduct.toEquiv_mulEquivSubgroup_symm`: `SemidirectProduct.mulEquivSubgroup` and
  `Subgroup.IsComplement.equiv` are mutually inverse modulo `SemidirectProduct.equivProd`.
* `SemidirectProduct.mulEquivSubgroup_symm_left`, `SemidirectProduct.mulEquivSubgroup_symm_right`,
  and `SemidirectProduct.rightHom_comp_mulEquivSubgroup_symm`: projections and quotient description
  of `(SemidirectProduct.mulEquivSubgroup h).symm`.
-/

public section

variable {G : Type*} [Group G] {H K : Subgroup G}

namespace Subgroup

open SemidirectProduct

/-- A normal subgroup of the first factor remains normal in the semidirect product if the
acting group preserves it. -/
theorem normal_map_inl {N Q : Type*} [Group N] [Group Q] {φ : Q →* MulAut N}
    (S : Subgroup N) [S.Normal] (hS : ∀ q n, n ∈ S → φ q n ∈ S) :
    (S.map (inl : N →* N ⋊[φ] Q)).Normal := by
  constructor
  rintro _ ⟨n, hn, rfl⟩ x
  refine ⟨x.left * φ x.right n * x.left⁻¹,
    ‹S.Normal›.conj_mem _ (hS _ _ hn) _, ?_⟩
  ext <;> simp [mul_assoc]

end Subgroup

namespace SemidirectProduct

/-- The lift of compatible homomorphisms evaluates a pair by multiplying the images of its
components. -/
@[simp]
theorem lift_apply {N D : Type*} [Group N] [Group D] {φ : G →* MulAut N}
    (f : N →* D) (g : G →* D)
    (h : ∀ b, f.comp (φ b).toMonoidHom = (MulAut.conj (g b)).toMonoidHom.comp f)
    (x : N ⋊[φ] G) : lift f g h x = f x.left * g x.right := by
  calc
    lift f g h x = lift f g h (inl x.left * inr x.right) := by
      rw [inl_left_mul_inr_right]
    _ = f x.left * g x.right := by rw [map_mul, lift_inl, lift_inr]

/-- Restricting subgroup multiplication to the left factor gives the subgroup inclusion. -/
@[simp]
theorem monoidHomSubgroup_comp_inl (hLE : K ≤ Subgroup.normalizer (H : Set G)) :
    (monoidHomSubgroup hLE).comp inl = H.subtype := by
  ext x
  simp

/-- Restricting subgroup multiplication to the right factor gives the subgroup inclusion. -/
@[simp]
theorem monoidHomSubgroup_comp_inr (hLE : K ≤ Subgroup.normalizer (H : Set G)) :
    (monoidHomSubgroup hLE).comp inr = K.subtype := by
  ext x
  simp

/-- Multiplication from the semidirect product of a subgroup with a subgroup normalizing it is onto
the join of the two subgroups. -/
@[simp]
theorem range_monoidHomSubgroup (hLE : K ≤ Subgroup.normalizer (H : Set G)) :
    (monoidHomSubgroup hLE).range = H ⊔ K := by
  refine le_antisymm ?_ (sup_le (fun x hx => ⟨inl ⟨x, hx⟩, by simp⟩)
    fun t ht => ⟨inr ⟨t, ht⟩, by simp⟩)
  rintro _ ⟨x, rfl⟩
  rw [monoidHomSubgroup_apply]
  exact Subgroup.mul_mem_sup x.left.2 x.right.2

/-- The kernel of the projection of a semidirect product to the acting group, together with the
image of the acting group, generates the semidirect product. -/
@[simp]
theorem ker_rightHom_sup_range_inr {N Q : Type*} [Group N] [Group Q] {φ : Q →* MulAut N} :
    (rightHom : N ⋊[φ] Q →* Q).ker ⊔ (inr : Q →* N ⋊[φ] Q).range = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  rw [← inl_left_mul_inr_right x]
  exact Subgroup.mul_mem_sup (by rw [← range_inl_eq_ker_rightHom]; exact ⟨_, rfl⟩) ⟨_, rfl⟩

section MonoidHomSubgroup

variable (hLE : K ≤ Subgroup.normalizer (H : Set G))

/-- The kernel of multiplication consists of the antidiagonal pairs in the intersection. -/
theorem mem_ker_monoidHomSubgroup_iff
    (x : H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hLE)] K) :
    x ∈ (monoidHomSubgroup hLE).ker ↔ (x.left : G) = (x.right : G)⁻¹ := by
  rw [MonoidHom.mem_ker, monoidHomSubgroup_apply, mul_eq_one_iff_eq_inv]

/-- Multiplication from `H ⋊ K` has trivial kernel precisely when `H` and `K` are disjoint. -/
@[simp]
theorem ker_monoidHomSubgroup_eq_bot_iff :
    (monoidHomSubgroup hLE).ker = ⊥ ↔ Disjoint H K := by
  rw [eq_bot_iff, disjoint_iff_inf_le]
  constructor
  · intro hker g ⟨hgH, hgK⟩
    let x : H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hLE)] K :=
      ⟨⟨g, hgH⟩, ⟨g⁻¹, K.inv_mem hgK⟩⟩
    have hx : x ∈ (monoidHomSubgroup hLE).ker := by
      rw [mem_ker_monoidHomSubgroup_iff]
      exact (inv_inv g).symm
    exact congrArg (fun y => (y.left : G)) (Subgroup.mem_bot.mp (hker hx))
  · intro hdisj x hx
    have hpair := (mem_ker_monoidHomSubgroup_iff hLE x).mp hx
    have hmem : (x.left : G) ∈ H ⊓ K :=
      ⟨x.left.property, hpair ▸ K.inv_mem x.right.property⟩
    have hl : (x.left : G) = 1 := Subgroup.mem_bot.mp (hdisj hmem)
    have hr : (x.right : G) = 1 := inv_eq_one.mp (hpair.symm.trans hl)
    exact SemidirectProduct.ext (Subtype.ext hl) (Subtype.ext hr)

/-- Multiplication from `H ⋊ K` is injective precisely when `H` and `K` are disjoint. -/
theorem injective_monoidHomSubgroup_iff :
    Function.Injective (monoidHomSubgroup hLE) ↔ Disjoint H K :=
  (MonoidHom.ker_eq_bot_iff _).symm.trans (ker_monoidHomSubgroup_eq_bot_iff hLE)

/-- Multiplication from `H ⋊ K` is surjective precisely when `H` and `K` generate `G`. -/
theorem surjective_monoidHomSubgroup_iff :
    Function.Surjective (monoidHomSubgroup hLE) ↔ H ⊔ K = ⊤ :=
  MonoidHom.range_eq_top.symm.trans (by rw [range_monoidHomSubgroup])

/-- Multiplication from `H ⋊ K` is bijective precisely when `H` and `K` are complements. -/
theorem bijective_monoidHomSubgroup_iff :
    Function.Bijective (monoidHomSubgroup hLE) ↔ H.IsComplement' K :=
  equivProd.bijective_comp fun x : H × K => (x.1 : G) * x.2

variable {D : Type*} [Group D]
variable (f : H →* D) (g : K →* D)
variable (hconj : ∀ b : K,
  f.comp (((H.normalizerMonoidHom).comp (Subgroup.inclusion hLE)) b).toMonoidHom =
    (MulAut.conj (g b)).toMonoidHom.comp f)

/-- The semidirect-product map kills the kernel of multiplication exactly when its two
restrictions agree on the intersection of the subgroups. -/
theorem ker_monoidHomSubgroup_le_ker_lift_iff :
    (monoidHomSubgroup hLE).ker ≤ (lift f g hconj).ker ↔
      ∀ a : ↥(H ⊓ K), f ⟨a, a.property.1⟩ = g ⟨a, a.property.2⟩ := by
  constructor
  · intro h a
    let x : H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hLE)] K :=
      ⟨⟨a, a.property.1⟩, ⟨(a : G)⁻¹, K.inv_mem a.property.2⟩⟩
    have hx : x ∈ (monoidHomSubgroup hLE).ker := by
      rw [mem_ker_monoidHomSubgroup_iff]
      exact (inv_inv (a : G)).symm
    have heq := MonoidHom.mem_ker.mp (h hx)
    -- Identify the explicitly constructed second component with inversion in K.
    have hr : x.right = (⟨a, a.property.2⟩ : K)⁻¹ :=
      Subtype.ext (Subgroup.coe_inv _ _).symm
    have hval : lift f g hconj x = f ⟨a, a.property.1⟩ * (g ⟨a, a.property.2⟩)⁻¹ := by
      rw [lift_apply, hr, map_inv]
    rw [hval, mul_inv_eq_one] at heq
    exact heq
  · intro hagree x hx
    have hpair := (mem_ker_monoidHomSubgroup_iff hLE x).mp hx
    have hright : (x.right : G) ∈ H := by
      rw [← inv_inv (x.right : G), ← hpair]
      exact H.inv_mem x.left.property
    have heq := hagree ⟨x.right, hright, x.right.property⟩
    have hleft : x.left = (⟨x.right, hright⟩ : H)⁻¹ :=
      Subtype.ext (hpair.trans (Subgroup.coe_inv _ _).symm)
    rw [MonoidHom.mem_ker, lift_apply, hleft, map_inv, heq, inv_mul_cancel]

end MonoidHomSubgroup

section MulEquivSubgroup

variable [H.Normal] (h : H.IsComplement' K)

/-- The underlying homomorphism of `SemidirectProduct.mulEquivSubgroup` is subgroup
multiplication. -/
@[simp]
theorem coe_mulEquivSubgroup :
    MonoidHom.ofClass (mulEquivSubgroup h) =
      monoidHomSubgroup (H.normalizer_eq_top ▸ le_top) := by
  ext x
  exact mulEquivSubgroup_apply h x

/-- As an equivalence of types, `SemidirectProduct.mulEquivSubgroup` factors through `H × K` via
the inverse of the complement decomposition `Subgroup.IsComplement.equiv`. -/
theorem toEquiv_mulEquivSubgroup :
    (mulEquivSubgroup h).toEquiv = equivProd.trans h.equiv.symm := by
  ext x
  exact mulEquivSubgroup_apply h x

/-- The inverse of `SemidirectProduct.mulEquivSubgroup` is the complement decomposition
`Subgroup.IsComplement.equiv` read in the semidirect product. -/
theorem toEquiv_mulEquivSubgroup_symm :
    (mulEquivSubgroup h).symm.toEquiv = h.equiv.trans equivProd.symm :=
  congrArg Equiv.symm (toEquiv_mulEquivSubgroup h)

/-- Evaluating `(SemidirectProduct.mulEquivSubgroup h).symm` decomposes an element into its normal
and complementary components. -/
theorem mulEquivSubgroup_symm_eq_equivProd_symm (g : G) :
    (mulEquivSubgroup h).symm g = equivProd.symm (h.equiv g) :=
  DFunLike.congr_fun (toEquiv_mulEquivSubgroup_symm h) g

/-- The left component of `(SemidirectProduct.mulEquivSubgroup h).symm` is the left component of
the complement decomposition. -/
theorem mulEquivSubgroup_symm_left (g : G) :
    ((mulEquivSubgroup h).symm g).left = (h.equiv g).1 :=
  congrArg left (mulEquivSubgroup_symm_eq_equivProd_symm h g)

/-- The right component of `(SemidirectProduct.mulEquivSubgroup h).symm` is the right component of
the complement decomposition. -/
theorem mulEquivSubgroup_symm_right (g : G) :
    ((mulEquivSubgroup h).symm g).right = (h.equiv g).2 :=
  congrArg right (mulEquivSubgroup_symm_eq_equivProd_symm h g)

/-- On the normal factor, `(SemidirectProduct.mulEquivSubgroup h).symm` agrees with
`SemidirectProduct.inl`. -/
theorem mulEquivSubgroup_symm_coe_left (x : H) :
    (mulEquivSubgroup h).symm (x : G) = inl x :=
  (MulEquiv.symm_apply_eq _).mpr (by simp)

/-- On the complementary factor, `(SemidirectProduct.mulEquivSubgroup h).symm` agrees with
`SemidirectProduct.inr`. -/
theorem mulEquivSubgroup_symm_coe_right (x : K) :
    (mulEquivSubgroup h).symm (x : G) = inr x :=
  (MulEquiv.symm_apply_eq _).mpr (by simp)

/-- Restricting `(SemidirectProduct.mulEquivSubgroup h).symm` to the normal factor gives
`SemidirectProduct.inl`. -/
@[simp]
theorem mulEquivSubgroup_symm_comp_subtype_left :
    (MonoidHom.ofClass (mulEquivSubgroup h).symm).comp H.subtype = inl :=
  MonoidHom.ext (mulEquivSubgroup_symm_coe_left h)

/-- Restricting `(SemidirectProduct.mulEquivSubgroup h).symm` to the complementary factor gives
`SemidirectProduct.inr`. -/
@[simp]
theorem mulEquivSubgroup_symm_comp_subtype_right :
    (MonoidHom.ofClass (mulEquivSubgroup h).symm).comp K.subtype = inr :=
  MonoidHom.ext (mulEquivSubgroup_symm_coe_right h)

/-- Projecting `(SemidirectProduct.mulEquivSubgroup h).symm` to the complementary factor agrees
with `Subgroup.IsComplement'.QuotientMulEquiv` after the quotient map. -/
@[simp]
theorem rightHom_comp_mulEquivSubgroup_symm :
    rightHom.comp (MonoidHom.ofClass (mulEquivSubgroup h).symm) =
      (MonoidHom.ofClass h.symm.QuotientMulEquiv).comp (QuotientGroup.mk' H) := by
  apply MonoidHom.ext
  intro g
  obtain ⟨z, rfl⟩ := (mulEquivSubgroup h).surjective g
  have hz : (QuotientGroup.mk' H) (z.left : G) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr z.left.property
  have hy : h.symm.QuotientMulEquiv.symm z.right = QuotientGroup.mk' H (z.right : G) :=
    h.symm.QuotientMulEquiv_symm_apply z.right
  rw [MonoidHom.comp_apply, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply, rightHom_eq_right,
    MonoidHom.comp_apply, MonoidHom.coe_ofClass, mulEquivSubgroup_apply, map_mul, hz, one_mul,
    ← hy, MulEquiv.apply_symm_apply]

end MulEquivSubgroup

end SemidirectProduct
