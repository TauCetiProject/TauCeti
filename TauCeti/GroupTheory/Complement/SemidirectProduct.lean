/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Local
public import TauCeti.GroupTheory.SemidirectProduct

/-!
# Semidirect-product decomposition of local and global complements

When `N` is normal in `H` and `K` is a local complement of `N` in `H`, `K` normalizes `N` in the
ambient group (`Subgroup.IsLocalComplement.right_le_normalizer`), and multiplication identifies
the external semidirect product `N ⋊ K` with `H`
(`Subgroup.IsLocalComplement.semidirectProductMulEquiv`). Its underlying equivalence of types is
the inverse of the product decomposition `Subgroup.IsLocalComplement.equiv`, so its inverse sends
`x : H` to the pair `(h.leftProjection x, h.rightProjection x)`.

When `H = ⊤` and `N` is normal in `G`, composing this local isomorphism with `Subgroup.topEquiv`
recovers Mathlib's `SemidirectProduct.mulEquivSubgroup`, identifying the inverse of
`SemidirectProduct.mulEquivSubgroup` with the local complement projections on `⊤`.

## Main definitions and results

* `Subgroup.IsLocalComplement.semidirectProductMulEquiv`: the multiplicative equivalence
  `N ⋊ K ≃* H` attached to a local complement `K` of `N` in `H` when `N` is normal in `H`.
* `Subgroup.IsLocalComplement.toEquiv_semidirectProductMulEquiv_symm`,
  `Subgroup.IsLocalComplement.semidirectProductMulEquiv_symm_left`, and
  `Subgroup.IsLocalComplement.semidirectProductMulEquiv_symm_right`: its inverse is the local
  product decomposition `(leftProjection, rightProjection)`.
* `Subgroup.IsLocalComplement.inclusion_comp_semidirectProductMulEquiv_restrict`: compatibility of
  the local semidirect-product decomposition with restriction to an intermediate subgroup.
* `Subgroup.IsLocalComplement.semidirectProductMulEquiv_top_trans_topEquiv` and
  `Subgroup.IsComplement'.mulEquivSubgroup_eq_semidirectProductMulEquiv_trans_topEquiv`: for
  `H = ⊤`, the local semidirect-product isomorphism agrees with
  `SemidirectProduct.mulEquivSubgroup`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] {N K H L : Subgroup G}

namespace IsLocalComplement

section SemidirectProduct

variable [(N.subgroupOf H).Normal] (h : N.IsLocalComplement K H)

/-- Multiplication identifies the semidirect product `N ⋊ K` with the ambient subgroup `H` of a
local complement when `N` is normal in `H`. -/
noncomputable def semidirectProductMulEquiv :
    N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K ≃* H :=
  { SemidirectProduct.equivProd.trans h.equiv.symm with
    map_mul' x y := Subtype.ext <| by
      have hm (z : N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K) :
          (h.equiv.symm (SemidirectProduct.equivProd z) : G) =
            SemidirectProduct.monoidHomSubgroup h.right_le_normalizer z :=
        (h.coe_equiv_symm_apply _).trans
          (SemidirectProduct.monoidHomSubgroup_apply h.right_le_normalizer z).symm
      exact (hm (x * y)).trans (((SemidirectProduct.monoidHomSubgroup
        h.right_le_normalizer).map_mul x y).trans (congrArg₂ (· * ·) (hm x).symm (hm y).symm)) }

/-- Evaluating `semidirectProductMulEquiv` multiplies the two subgroup components in `G`. -/
@[simp]
theorem coe_semidirectProductMulEquiv_apply
    (x : N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K) :
    (h.semidirectProductMulEquiv x : G) = (x.left : G) * x.right :=
  h.coe_equiv_symm_apply (SemidirectProduct.equivProd x)

/-- Following `semidirectProductMulEquiv` by `H.subtype` gives
`SemidirectProduct.monoidHomSubgroup`. -/
@[simp]
theorem subtype_comp_semidirectProductMulEquiv :
    H.subtype.comp (MonoidHom.ofClass h.semidirectProductMulEquiv) =
      SemidirectProduct.monoidHomSubgroup h.right_le_normalizer :=
  MonoidHom.ext h.coe_semidirectProductMulEquiv_apply

/-- On the left factor `N`, `semidirectProductMulEquiv` is the subgroup inclusion `N →* H`. -/
@[simp]
theorem semidirectProductMulEquiv_inl (n : N) :
    h.semidirectProductMulEquiv (SemidirectProduct.inl n) = inclusion h.left_le n :=
  Subtype.ext (by simp)

/-- On the right factor `K`, `semidirectProductMulEquiv` is the subgroup inclusion `K →* H`. -/
@[simp]
theorem semidirectProductMulEquiv_inr (k : K) :
    h.semidirectProductMulEquiv (SemidirectProduct.inr k) = inclusion h.right_le k :=
  Subtype.ext (by simp)

/-- Restricting `semidirectProductMulEquiv` to the left factor gives `inclusion h.left_le`. -/
@[simp]
theorem semidirectProductMulEquiv_comp_inl :
    (MonoidHom.ofClass h.semidirectProductMulEquiv).comp SemidirectProduct.inl =
      inclusion h.left_le :=
  MonoidHom.ext h.semidirectProductMulEquiv_inl

/-- Restricting `semidirectProductMulEquiv` to the right factor gives `inclusion h.right_le`. -/
@[simp]
theorem semidirectProductMulEquiv_comp_inr :
    (MonoidHom.ofClass h.semidirectProductMulEquiv).comp SemidirectProduct.inr =
      inclusion h.right_le :=
  MonoidHom.ext h.semidirectProductMulEquiv_inr

/-- As an equivalence of types, `semidirectProductMulEquiv` is the inverse of `h.equiv` modulo
`SemidirectProduct.equivProd`. -/
theorem toEquiv_semidirectProductMulEquiv :
    h.semidirectProductMulEquiv.toEquiv = SemidirectProduct.equivProd.trans h.equiv.symm := (rfl)

/-- As an equivalence of types, `semidirectProductMulEquiv.symm` is the local decomposition
`h.equiv` read in `N ⋊ K`. -/
theorem toEquiv_semidirectProductMulEquiv_symm :
    h.semidirectProductMulEquiv.symm.toEquiv = h.equiv.trans SemidirectProduct.equivProd.symm :=
  (rfl)

/-- Evaluating `semidirectProductMulEquiv.symm` sends `x : H` to `h.equiv x` in `N ⋊ K`. -/
theorem semidirectProductMulEquiv_symm_eq_equivProd_symm (x : H) :
    h.semidirectProductMulEquiv.symm x = SemidirectProduct.equivProd.symm (h.equiv x) := (rfl)

/-- The left component of `semidirectProductMulEquiv.symm` is `h.leftProjection`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_left (x : H) :
    (h.semidirectProductMulEquiv.symm x).left = h.leftProjection x :=
  (h.leftProjection_apply x).symm

/-- The right component of `semidirectProductMulEquiv.symm` is `h.rightProjection`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_right (x : H) :
    (h.semidirectProductMulEquiv.symm x).right = h.rightProjection x :=
  (h.rightProjection_apply x).symm

/-- Projecting `semidirectProductMulEquiv.symm` to the acting subgroup gives `h.rightProjection`. -/
@[simp]
theorem rightHom_comp_semidirectProductMulEquiv_symm :
    SemidirectProduct.rightHom.comp (MonoidHom.ofClass h.semidirectProductMulEquiv.symm) =
      h.rightProjection :=
  MonoidHom.ext h.semidirectProductMulEquiv_symm_right

/-- On `N ≤ H`, `semidirectProductMulEquiv.symm` agrees with `SemidirectProduct.inl`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_inclusion_left (n : N) :
    h.semidirectProductMulEquiv.symm (inclusion h.left_le n) = SemidirectProduct.inl n :=
  (MulEquiv.symm_apply_eq _).mpr (h.semidirectProductMulEquiv_inl n).symm

/-- On `K ≤ H`, `semidirectProductMulEquiv.symm` agrees with `SemidirectProduct.inr`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_inclusion_right (k : K) :
    h.semidirectProductMulEquiv.symm (inclusion h.right_le k) = SemidirectProduct.inr k :=
  (MulEquiv.symm_apply_eq _).mpr (h.semidirectProductMulEquiv_inr k).symm

/-- Restricting `semidirectProductMulEquiv.symm` along `N ≤ H` gives `SemidirectProduct.inl`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_comp_inclusion_left :
    (MonoidHom.ofClass h.semidirectProductMulEquiv.symm).comp (inclusion h.left_le) =
      SemidirectProduct.inl :=
  MonoidHom.ext h.semidirectProductMulEquiv_symm_inclusion_left

/-- Restricting `semidirectProductMulEquiv.symm` along `K ≤ H` gives `SemidirectProduct.inr`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_comp_inclusion_right :
    (MonoidHom.ofClass h.semidirectProductMulEquiv.symm).comp (inclusion h.right_le) =
      SemidirectProduct.inr :=
  MonoidHom.ext h.semidirectProductMulEquiv_symm_inclusion_right

/-- Restricting a local complement to an intermediate subgroup `N ≤ L ≤ H` intertwines the
semidirect-product decompositions along the subgroup inclusions. -/
theorem inclusion_comp_semidirectProductMulEquiv_restrict [(N.subgroupOf L).Normal]
    (hNL : N ≤ L) (hLH : L ≤ H) :
    (inclusion hLH).comp (MonoidHom.ofClass (h.restrict hNL hLH).semidirectProductMulEquiv) =
      (MonoidHom.ofClass h.semidirectProductMulEquiv).comp
        (SemidirectProduct.map (MonoidHom.id N) (inclusion inf_le_left) fun _ => by ext; simp) :=
  MonoidHom.ext fun _ => Subtype.ext (by simp)

/-- Restricting a local complement to `N ≤ L ≤ H` intertwines the inverse semidirect-product
decompositions. -/
theorem map_comp_semidirectProductMulEquiv_restrict_symm [(N.subgroupOf L).Normal]
    (hNL : N ≤ L) (hLH : L ≤ H) :
    (SemidirectProduct.map (MonoidHom.id N) (inclusion inf_le_left) fun _ => by ext; simp).comp
        (MonoidHom.ofClass (h.restrict hNL hLH).semidirectProductMulEquiv.symm) =
      (MonoidHom.ofClass h.semidirectProductMulEquiv.symm).comp (inclusion hLH) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (h.restrict hNL hLH).semidirectProductMulEquiv.surjective x
  have hfwd :=
    DFunLike.congr_fun (h.inclusion_comp_semidirectProductMulEquiv_restrict hNL hLH) y
  simp only [MonoidHom.comp_apply, MonoidHom.coe_ofClass] at hfwd ⊢
  rw [MulEquiv.symm_apply_apply, hfwd, MulEquiv.symm_apply_apply]

end SemidirectProduct

/-- For `H = ⊤`, composing the local semidirect-product isomorphism with `Subgroup.topEquiv`
recovers `SemidirectProduct.mulEquivSubgroup`. -/
@[simp]
theorem semidirectProductMulEquiv_top_trans_topEquiv [N.Normal] (h : N.IsLocalComplement K ⊤) :
    h.semidirectProductMulEquiv.trans topEquiv =
      SemidirectProduct.mulEquivSubgroup (isLocalComplement_top_iff.mp h) :=
  MulEquiv.ext fun x =>
    (h.coe_semidirectProductMulEquiv_apply x).trans
      (SemidirectProduct.mulEquivSubgroup_apply (isLocalComplement_top_iff.mp h) x).symm

end IsLocalComplement

namespace IsComplement'

variable [N.Normal] {D : Subgroup G} (h : N.IsComplement' D)

/-- `SemidirectProduct.mulEquivSubgroup` factors through the local semidirect-product isomorphism
on `⊤` followed by `Subgroup.topEquiv`. -/
theorem mulEquivSubgroup_eq_semidirectProductMulEquiv_trans_topEquiv :
    SemidirectProduct.mulEquivSubgroup h =
      (isLocalComplement_top_iff.mpr h).semidirectProductMulEquiv.trans topEquiv :=
  ((isLocalComplement_top_iff.mpr h).semidirectProductMulEquiv_top_trans_topEquiv).symm

/-- The left component of `(SemidirectProduct.mulEquivSubgroup h).symm` is the local left
projection on `⊤`. -/
theorem mulEquivSubgroup_symm_left_eq_leftProjection (g : G) :
    ((SemidirectProduct.mulEquivSubgroup h).symm g).left =
      (isLocalComplement_top_iff.mpr h).leftProjection ⟨g, mem_top g⟩ :=
  (SemidirectProduct.mulEquivSubgroup_symm_left h g).trans
    ((isLocalComplement_top_iff.mpr h).leftProjection_top ⟨g, mem_top g⟩).symm

/-- The right component of `(SemidirectProduct.mulEquivSubgroup h).symm` is the local right
projection on `⊤`. -/
theorem mulEquivSubgroup_symm_right_eq_rightProjection (g : G) :
    ((SemidirectProduct.mulEquivSubgroup h).symm g).right =
      (isLocalComplement_top_iff.mpr h).rightProjection ⟨g, mem_top g⟩ :=
  (SemidirectProduct.mulEquivSubgroup_symm_right h g).trans
    ((isLocalComplement_top_iff.mpr h).rightProjection_top ⟨g, mem_top g⟩).symm

/-- The right component of `(SemidirectProduct.mulEquivSubgroup h).symm` is given by the quotient
isomorphism `Subgroup.IsComplement'.QuotientMulEquiv`. -/
theorem mulEquivSubgroup_symm_right_eq_quotientMulEquiv (g : G) :
    ((SemidirectProduct.mulEquivSubgroup h).symm g).right = h.symm.QuotientMulEquiv g :=
  (SemidirectProduct.mulEquivSubgroup_symm_right h g).trans (h.equiv_snd_eq_quotientMulEquiv g)

end IsComplement'

end Subgroup
