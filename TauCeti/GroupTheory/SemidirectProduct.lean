/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Semidirect products, normalizing subgroups, and complementary decompositions

Let `H` and `K` be subgroups of a group `G` with `K ≤ Subgroup.normalizer H`. Multiplication then
carries the external semidirect product `H ⋊ K` into `G` (`SemidirectProduct.monoidHomSubgroup`),
its image is the join `H ⊔ K`, and it is injective precisely when `H` and `K` are disjoint. The
corresponding elementwise normal form of `H ⊔ K` is
`Subgroup.mem_sup_of_right_le_normalizer_left` in `TauCeti.Algebra.Group.Subgroup.Pointwise`.
When `H` is normal and `H.IsComplement' K`, the isomorphism `SemidirectProduct.mulEquivSubgroup`
is inverse to the complement decomposition `Subgroup.IsComplement.equiv`, and its right component
factors through `QuotientGroup.mk' H` and `Subgroup.IsComplement'.QuotientMulEquiv`.
An invariant normal subgroup of the first factor is normal in the full semidirect product
(`Subgroup.normal_map_inl`).

## Main results

* `SemidirectProduct.lift_apply`: the external lift evaluates a pair by multiplying the
  images of its components.
* `SemidirectProduct.range_monoidHomSubgroup`: the range of the semidirect-product
  multiplication homomorphism is `H ⊔ K`.
* `SemidirectProduct.ker_rightHom_sup_range_inr`: the kernel of the projection to the acting group
  and the acting group generate the semidirect product.
* `SemidirectProduct.mem_ker_monoidHomSubgroup_iff` and
  `SemidirectProduct.ker_monoidHomSubgroup_eq_bot_iff`: its kernel consists of antidiagonal pairs
  and is trivial if and only if `Disjoint H K`.
* `SemidirectProduct.ker_monoidHomSubgroup_le_ker_lift_iff`: an external lift kills this kernel
  exactly when the two maps agree on the intersection.
* `SemidirectProduct.toEquiv_mulEquivSubgroup_symm` and
  `SemidirectProduct.mulEquivSubgroup_symm_eq_inl_mul_inr`: the inverse of
  `SemidirectProduct.mulEquivSubgroup` agrees with `Subgroup.IsComplement.equiv`.
* `SemidirectProduct.rightHom_comp_mulEquivSubgroup_symm`: projecting the inverse of
  `SemidirectProduct.mulEquivSubgroup` to `K` factors through `G ⧸ H`.
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

/-- Multiplication from the semidirect product has trivial kernel if and only if the two
subgroups are disjoint. -/
@[simp]
theorem ker_monoidHomSubgroup_eq_bot_iff :
    (monoidHomSubgroup hLE).ker = ⊥ ↔ Disjoint H K := by
  rw [Subgroup.eq_bot_iff_forall]
  constructor
  · rw [disjoint_iff_inf_le]
    intro hker g hg
    have hx : (⟨⟨g, hg.1⟩, ⟨g⁻¹, K.inv_mem hg.2⟩⟩ :
        H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hLE)] K) ∈
          (monoidHomSubgroup hLE).ker := by
      rw [mem_ker_monoidHomSubgroup_iff]
      exact (inv_inv g).symm
    exact congrArg (fun y : H => (y : G)) (congrArg SemidirectProduct.left (hker _ hx))
  · intro hdisj x hx
    rw [MonoidHom.mem_ker, monoidHomSubgroup_apply] at hx
    obtain ⟨hl, hr⟩ :=
      Subgroup.disjoint_iff_mul_eq_one.mp hdisj x.left.property x.right.property hx
    ext <;> simp [hl, hr]

/-- Multiplication from the semidirect product is injective if and only if the two subgroups are
disjoint. -/
@[simp]
theorem monoidHomSubgroup_injective_iff :
    Function.Injective (monoidHomSubgroup hLE) ↔ Disjoint H K := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_monoidHomSubgroup_eq_bot_iff]

variable {D : Type*} [Group D] (f : H →* D) (g : K →* D)
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

/-- As a bijection of types, `SemidirectProduct.mulEquivSubgroup` is `equivProd` followed by the
inverse of the complement decomposition `Subgroup.IsComplement.equiv`. -/
theorem toEquiv_mulEquivSubgroup :
    (mulEquivSubgroup h).toEquiv = equivProd.trans h.equiv.symm := by
  ext x
  exact (mulEquivSubgroup_apply h x).trans
    (Subgroup.IsComplement.equiv_symm_apply h (x.1, x.2)).symm

/-- The inverse of `SemidirectProduct.mulEquivSubgroup` is the complement decomposition
`Subgroup.IsComplement.equiv` followed by `equivProd.symm`. -/
theorem toEquiv_mulEquivSubgroup_symm :
    (mulEquivSubgroup h).symm.toEquiv = h.equiv.trans equivProd.symm := by
  ext g : 1
  apply (mulEquivSubgroup h).injective
  exact ((mulEquivSubgroup h).apply_symm_apply g).trans (h.equiv_fst_mul_equiv_snd g).symm

/-- The left component of `(mulEquivSubgroup h).symm` is the first factor of the complement
decomposition. -/
theorem left_mulEquivSubgroup_symm (g : G) :
    ((mulEquivSubgroup h).symm g).left = (h.equiv g).1 :=
  congrArg SemidirectProduct.left (Equiv.congr_fun (toEquiv_mulEquivSubgroup_symm h) g)

/-- The right component of `(mulEquivSubgroup h).symm` is the second factor of the complement
decomposition. -/
theorem right_mulEquivSubgroup_symm (g : G) :
    ((mulEquivSubgroup h).symm g).right = (h.equiv g).2 :=
  congrArg SemidirectProduct.right (Equiv.congr_fun (toEquiv_mulEquivSubgroup_symm h) g)

/-- Evaluating `(mulEquivSubgroup h).symm` decomposes a group element into its normal and
complementary factors inside the semidirect product. -/
theorem mulEquivSubgroup_symm_eq_inl_mul_inr (g : G) :
    (mulEquivSubgroup h).symm g = inl (h.equiv g).1 * inr (h.equiv g).2 := by
  rw [← left_mulEquivSubgroup_symm, ← right_mulEquivSubgroup_symm, inl_left_mul_inr_right]

/-- Restricting `mulEquivSubgroup` to the left factor gives the subgroup inclusion. -/
@[simp]
theorem mulEquivSubgroup_comp_inl :
    (MonoidHom.ofClass (mulEquivSubgroup h)).comp inl = H.subtype := by
  ext a
  simp

/-- Restricting `mulEquivSubgroup` to the right factor gives the subgroup inclusion. -/
@[simp]
theorem mulEquivSubgroup_comp_inr :
    (MonoidHom.ofClass (mulEquivSubgroup h)).comp inr = K.subtype := by
  ext b
  simp

/-- The inverse of `mulEquivSubgroup` sends an element of the normal subgroup to the left
factor. -/
theorem mulEquivSubgroup_symm_coe_left (a : H) :
    (mulEquivSubgroup h).symm (a : G) = inl a := by
  rw [MulEquiv.symm_apply_eq]
  simp

/-- The inverse of `mulEquivSubgroup` sends an element of the complement to the right factor. -/
theorem mulEquivSubgroup_symm_coe_right (b : K) :
    (mulEquivSubgroup h).symm (b : G) = inr b := by
  rw [MulEquiv.symm_apply_eq]
  simp

/-- Restricting `(mulEquivSubgroup h).symm` to the normal subgroup gives `inl`. -/
@[simp]
theorem mulEquivSubgroup_symm_comp_left_subtype :
    (MonoidHom.ofClass (mulEquivSubgroup h).symm).comp H.subtype = inl := by
  apply MonoidHom.ext
  intro a
  exact mulEquivSubgroup_symm_coe_left h a

/-- Restricting `(mulEquivSubgroup h).symm` to the complement gives `inr`. -/
@[simp]
theorem mulEquivSubgroup_symm_comp_right_subtype :
    (MonoidHom.ofClass (mulEquivSubgroup h).symm).comp K.subtype = inr := by
  apply MonoidHom.ext
  intro b
  exact mulEquivSubgroup_symm_coe_right h b

/-- Composing `mulEquivSubgroup` with the quotient map factors through `rightHom` and the
quotient isomorphism of the complement. -/
theorem quotientGroupMk'_comp_mulEquivSubgroup :
    (QuotientGroup.mk' H).comp (mulEquivSubgroup h).toMonoidHom =
      h.symm.QuotientMulEquiv.symm.toMonoidHom.comp rightHom := by
  apply hom_ext
  · apply MonoidHom.ext
    intro a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mulEquivSubgroup_apply, left_inl,
      right_inl, OneMemClass.coe_one, mul_one, rightHom_inl, map_one, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (a : G)).mpr a.property
  · apply MonoidHom.ext
    intro b
    have hb : h.symm.QuotientMulEquiv.symm b = ((b : G) : G ⧸ H) :=
      h.symm.QuotientMulEquiv_symm_apply b
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mulEquivSubgroup_apply, left_inr,
      right_inr, OneMemClass.coe_one, one_mul, rightHom_inr, QuotientGroup.mk'_apply, hb]

/-- Projecting `(mulEquivSubgroup h).symm` to the acting factor factors through the quotient by
the normal subgroup. -/
theorem rightHom_comp_mulEquivSubgroup_symm :
    rightHom.comp (mulEquivSubgroup h).symm.toMonoidHom =
      h.symm.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' H) := by
  apply MonoidHom.ext
  intro g
  apply h.symm.QuotientMulEquiv.symm.injective
  have hq := DFunLike.congr_fun (quotientGroupMk'_comp_mulEquivSubgroup h)
    ((mulEquivSubgroup h).symm g)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    MulEquiv.symm_apply_apply] using hq.symm

/-- The right component of `(mulEquivSubgroup h).symm` agrees with the quotient isomorphism
evaluated on the coset. -/
theorem right_mulEquivSubgroup_symm_eq_quotientMulEquiv (g : G) :
    ((mulEquivSubgroup h).symm g).right = h.symm.QuotientMulEquiv (g : G ⧸ H) :=
  DFunLike.congr_fun (rightHom_comp_mulEquivSubgroup_symm h) g

end MulEquivSubgroup

end SemidirectProduct
