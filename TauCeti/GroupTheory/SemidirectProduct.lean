/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
import TauCeti.GroupTheory.Complement.Basic

/-!
# Semidirect products and multiplication of normalizing subgroups

Let `H` and `K` be subgroups of a group `G` with `K ≤ Subgroup.normalizer H`. Multiplication then
carries the external semidirect product `H ⋊ K` into `G` (`SemidirectProduct.monoidHomSubgroup`),
with image `H ⊔ K` and kernel trivial precisely when `H` and `K` are disjoint, so it is bijective
precisely when `H.IsComplement' K`. The corresponding elementwise normal form of `H ⊔ K` is
`Subgroup.mem_sup_of_right_le_normalizer_left` in `TauCeti.Algebra.Group.Subgroup.Pointwise`.
An invariant normal subgroup of the first factor is normal in the full semidirect product
(`Subgroup.normal_map_inl`). When `D` is a complement of a normal subgroup `N`, the inverse of
Mathlib's isomorphism `SemidirectProduct.mulEquivSubgroup : N ⋊ D ≃* G` is the unique
decomposition `g = n * d` of `Subgroup.IsComplement.equiv`, and projecting it to `D` factors
through `G ⧸ N` via `Subgroup.IsComplement'.QuotientMulEquiv`.

## Main results

* `SemidirectProduct.lift_apply`: the external lift evaluates a pair by multiplying the
  images of its components.
* `SemidirectProduct.range_monoidHomSubgroup`: the range of the semidirect-product
  multiplication homomorphism is `H ⊔ K`.
* `SemidirectProduct.ker_rightHom_sup_range_inr`: the kernel of the projection to the acting group
  and the acting group generate the semidirect product.
* `SemidirectProduct.infinite_range_inl`: the image of the normal factor is infinite whenever the
  normal factor is infinite.
* `SemidirectProduct.mem_ker_monoidHomSubgroup_iff`: its kernel consists of antidiagonal pairs.
* `SemidirectProduct.ker_monoidHomSubgroup_eq_bot_iff`: its kernel is trivial precisely when `H`
  and `K` are disjoint.
* `SemidirectProduct.monoidHomSubgroup_bijective_iff`: multiplication from `H ⋊ K` is bijective
  precisely when `H.IsComplement' K`.
* `SemidirectProduct.ker_monoidHomSubgroup_le_ker_lift_iff`: an external lift kills this kernel
  precisely when the two maps agree on the intersection.
* `SemidirectProduct.mulEquivSubgroup_symm_trans_equivProd`: for a complement `D` of a normal
  subgroup `N`, the inverse of `N ⋊ D ≃* G` followed by `SemidirectProduct.equivProd` is the
  complement decomposition `G ≃ N × D`.
* `SemidirectProduct.toEquiv_mulEquivSubgroup`,
  `SemidirectProduct.toEquiv_mulEquivSubgroup_symm`: `SemidirectProduct.mulEquivSubgroup` and
  `Subgroup.IsComplement.equiv` are mutually inverse up to `SemidirectProduct.equivProd`.
* `SemidirectProduct.rightHom_comp_mulEquivSubgroup_symm`: projecting
  `(SemidirectProduct.mulEquivSubgroup h).symm` to `D` factors through `G ⧸ N` via
  `Subgroup.IsComplement'.QuotientMulEquiv`.
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

/-- The kernel of the projection of a semidirect product to the acting group, together with the
image of the acting group, generates the semidirect product. -/
@[simp]
theorem ker_rightHom_sup_range_inr {N Q : Type*} [Group N] [Group Q] {φ : Q →* MulAut N} :
    (rightHom : N ⋊[φ] Q →* Q).ker ⊔ (inr : Q →* N ⋊[φ] Q).range = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  rw [← inl_left_mul_inr_right x]
  exact Subgroup.mul_mem_sup (by rw [← range_inl_eq_ker_rightHom]; exact ⟨_, rfl⟩) ⟨_, rfl⟩

section MonoidHomSubgroup

/-- If `N` is infinite, then the image of `SemidirectProduct.inl` in `N ⋊[φ] Q` is infinite. -/
theorem infinite_range_inl {N Q : Type*} [Group N] [Infinite N] [Group Q] {φ : Q →* MulAut N} :
    Infinite (inl : N →* N ⋊[φ] Q).range :=
  (Equiv.ofBijective (inl : N →* N ⋊[φ] Q).rangeRestrict
    ⟨fun _ _ h ↦ inl_injective (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩).infinite_iff.mp ‹_›

variable {D : Type*} [Group D]
variable (hLE : K ≤ Subgroup.normalizer (H : Set G))

/-- Multiplication from the semidirect product of a subgroup with a subgroup normalizing it is onto
the join of the two subgroups. -/
@[simp]
theorem range_monoidHomSubgroup :
    (monoidHomSubgroup hLE).range = H ⊔ K := by
  refine le_antisymm ?_ (sup_le (fun x hx => ⟨inl ⟨x, hx⟩, by simp⟩)
    fun t ht => ⟨inr ⟨t, ht⟩, by simp⟩)
  rintro _ ⟨x, rfl⟩
  rw [monoidHomSubgroup_apply]
  exact Subgroup.mul_mem_sup x.left.2 x.right.2

/-- Multiplication from the semidirect product of a subgroup with a normalizing subgroup is
surjective precisely when the two subgroups generate the ambient group. -/
theorem monoidHomSubgroup_surjective_iff :
    Function.Surjective (monoidHomSubgroup hLE) ↔ H ⊔ K = ⊤ := by
  rw [← MonoidHom.range_eq_top, range_monoidHomSubgroup]

/-- The kernel of multiplication consists of the antidiagonal pairs in the intersection. -/
theorem mem_ker_monoidHomSubgroup_iff
    (x : H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hLE)] K) :
    x ∈ (monoidHomSubgroup hLE).ker ↔ (x.left : G) = (x.right : G)⁻¹ := by
  rw [MonoidHom.mem_ker, monoidHomSubgroup_apply, mul_eq_one_iff_eq_inv]

/-- Multiplication from the semidirect product of a subgroup with a normalizing subgroup has
trivial kernel precisely when the two subgroups are disjoint. -/
@[simp]
theorem ker_monoidHomSubgroup_eq_bot_iff :
    (monoidHomSubgroup hLE).ker = ⊥ ↔ Disjoint H K := by
  rw [Subgroup.eq_bot_iff_forall, Subgroup.disjoint_iff_mul_eq_one]
  refine ⟨fun h x y hx hy hxy ↦ ?_, fun h x hx ↦ ?_⟩
  · have h1 := h ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ (by simpa [MonoidHom.mem_ker] using hxy)
    exact ⟨by simpa using congrArg left h1, by simpa using congrArg right h1⟩
  · obtain ⟨hl, hr⟩ := h x.left.2 x.right.2 (by simpa [MonoidHom.mem_ker] using hx)
    ext <;> assumption

/-- Multiplication from the semidirect product of a subgroup with a normalizing subgroup is
injective precisely when the two subgroups are disjoint. -/
theorem monoidHomSubgroup_injective_iff :
    Function.Injective (monoidHomSubgroup hLE) ↔ Disjoint H K := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_monoidHomSubgroup_eq_bot_iff]

/-- Multiplication from the semidirect product of a subgroup with a normalizing subgroup is
bijective precisely when the two subgroups are complements. -/
theorem monoidHomSubgroup_bijective_iff :
    Function.Bijective (monoidHomSubgroup hLE) ↔ H.IsComplement' K :=
  equivProd.bijective_comp (fun x : H × K => (x.1 : G) * x.2)

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

variable {N : Subgroup G} [N.Normal] {D : Subgroup G} (h : N.IsComplement' D)

/-- The underlying homomorphism of `SemidirectProduct.mulEquivSubgroup` is
`SemidirectProduct.monoidHomSubgroup`. -/
theorem toMonoidHom_mulEquivSubgroup :
    (mulEquivSubgroup h).toMonoidHom = monoidHomSubgroup (N.normalizer_eq_top ▸ le_top) := by
  ext x
  simp

/-- The inverse of `mulEquivSubgroup h` sends `g` to its complement decomposition `g = n * d`,
read as a pair in the semidirect product. -/
theorem mulEquivSubgroup_symm_apply_eq (g : G) :
    (mulEquivSubgroup h).symm g = equivProd.symm (h.equiv g) := by
  apply (mulEquivSubgroup h).injective
  rw [MulEquiv.apply_symm_apply, mulEquivSubgroup_apply]
  exact (h.equiv_fst_mul_equiv_snd g).symm

/-- The normal component of `(mulEquivSubgroup h).symm g` is the `N`-factor of `g = n * d`. -/
theorem mulEquivSubgroup_symm_apply_left (g : G) :
    ((mulEquivSubgroup h).symm g).left = (h.equiv g).1 := by
  rw [mulEquivSubgroup_symm_apply_eq, equivProd_symm_apply_left]

/-- The acting component of `(mulEquivSubgroup h).symm g` is the `D`-factor of `g = n * d`. -/
theorem mulEquivSubgroup_symm_apply_right (g : G) :
    ((mulEquivSubgroup h).symm g).right = (h.equiv g).2 := by
  rw [mulEquivSubgroup_symm_apply_eq, equivProd_symm_apply_right]

/-- The isomorphism `N ⋊ D ≃* G` of complementary subgroups is inverse to the complement
decomposition: its inverse, followed by the identification of `N ⋊ D` with `N × D` as types, is
`Subgroup.IsComplement.equiv`. -/
theorem mulEquivSubgroup_symm_trans_equivProd :
    (mulEquivSubgroup h).symm.toEquiv.trans equivProd = h.equiv :=
  Equiv.ext fun g =>
    (congrArg equivProd (mulEquivSubgroup_symm_apply_eq h g)).trans (equivProd.apply_symm_apply _)

/-- As an equivalence of types, `(SemidirectProduct.mulEquivSubgroup h).symm` is the complement
decomposition `Subgroup.IsComplement.equiv` followed by `equivProd.symm`. -/
theorem toEquiv_mulEquivSubgroup_symm :
    (mulEquivSubgroup h).symm.toEquiv = h.equiv.trans equivProd.symm :=
  Equiv.ext (mulEquivSubgroup_symm_apply_eq h)

/-- As an equivalence of types, `SemidirectProduct.mulEquivSubgroup` is `equivProd` followed by
the inverse of the complement decomposition `Subgroup.IsComplement.equiv`. -/
theorem toEquiv_mulEquivSubgroup :
    (mulEquivSubgroup h).toEquiv = equivProd.trans h.equiv.symm :=
  congrArg Equiv.symm (toEquiv_mulEquivSubgroup_symm h)

/-- `(SemidirectProduct.mulEquivSubgroup h).symm` decomposes an element into the product of its
left and right subgroup components inside the semidirect product. -/
theorem mulEquivSubgroup_symm_eq_inl_mul_inr (g : G) :
    (mulEquivSubgroup h).symm g = inl (h.equiv g).1 * inr (h.equiv g).2 := by
  rw [← inl_left_mul_inr_right ((mulEquivSubgroup h).symm g), mulEquivSubgroup_symm_apply_left,
    mulEquivSubgroup_symm_apply_right]

/-- `(SemidirectProduct.mulEquivSubgroup h).symm` maps an element of the normal factor `N` to
`inl`. -/
theorem mulEquivSubgroup_symm_coe_left (a : N) :
    (mulEquivSubgroup h).symm a = inl a := by
  rw [(mulEquivSubgroup h).symm_apply_eq]
  simp

/-- `(SemidirectProduct.mulEquivSubgroup h).symm` maps an element of the complementary factor `D`
to `inr`. -/
theorem mulEquivSubgroup_symm_coe_right (b : D) :
    (mulEquivSubgroup h).symm b = inr b := by
  rw [(mulEquivSubgroup h).symm_apply_eq]
  simp

/-- Restricting `(SemidirectProduct.mulEquivSubgroup h).symm` to `N` recovers `inl`. -/
@[simp]
theorem mulEquivSubgroup_symm_comp_left_subtype :
    ((mulEquivSubgroup h).symm :
      G →* N ⋊[(N.normalizerMonoidHom).comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))]
        D).comp N.subtype = inl := by
  apply MonoidHom.ext
  intro a
  exact mulEquivSubgroup_symm_coe_left h a

/-- Restricting `(SemidirectProduct.mulEquivSubgroup h).symm` to `D` recovers `inr`. -/
@[simp]
theorem mulEquivSubgroup_symm_comp_right_subtype :
    ((mulEquivSubgroup h).symm :
      G →* N ⋊[(N.normalizerMonoidHom).comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))]
        D).comp D.subtype = inr := by
  apply MonoidHom.ext
  intro b
  exact mulEquivSubgroup_symm_coe_right h b

/-- Projecting `(SemidirectProduct.mulEquivSubgroup h).symm` to the acting complement `D` factors
through the quotient `G ⧸ N` via `Subgroup.IsComplement'.QuotientMulEquiv`. -/
@[simp]
theorem rightHom_comp_mulEquivSubgroup_symm :
    rightHom.comp ((mulEquivSubgroup h).symm :
      G →* N ⋊[(N.normalizerMonoidHom).comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))]
        D) =
      (h.symm.QuotientMulEquiv : G ⧸ N →* D).comp (QuotientGroup.mk' N) := by
  ext g
  simp [mulEquivSubgroup_symm_apply_right, h.symm_quotientMulEquiv_mk,
    -mulEquivSubgroup_symm_apply]

end MulEquivSubgroup

end SemidirectProduct
