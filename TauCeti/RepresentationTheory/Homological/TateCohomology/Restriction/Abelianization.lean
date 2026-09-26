/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupHomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Abelianization
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Basic

/-!
# Restriction and corestriction in Tate degree `-2` on the abelianization

For a finite group `G` and trivial coefficients `A`, degree `-2` Tate cohomology is
`Ĥ⁻²(G, A) ≃ Gᵃᵇ ⊗ A` (`TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial`). This file
identifies the two change-of-group maps in this degree under that identification:

* restriction to a subgroup `S ≤ G`, `Ĥ⁻²(G, A) ⟶ Ĥ⁻²(S, A)`, is the group-theoretic transfer
  (Verlagerung) `Gᵃᵇ → Sᵃᵇ`, tensored with `A`;
* corestriction along a homomorphism `f : H →* G`, `Ĥ⁻²(H, A) ⟶ Ĥ⁻²(G, A)`, is
  `Abelianization.map f`, tensored with `A`.

Both are read off the corresponding statements for first group homology,
`TauCeti.groupHomology.H1AddEquivOfIsTrivial_transfer` and
`TauCeti.groupHomology.H1AddEquivOfIsTrivial_map`, through the comparison of negative Tate degrees
with group homology. For `A = ℤ` these are the forms in which the reciprocity isomorphism
`Ĥ⁻²(G, ℤ) ≃ Gᵃᵇ` is compatible with restriction and corestriction.

## Main results

* `TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial_HNegTwoRes`: restriction in degree `-2`
  is the Verlagerung.
* `TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial_HNegTwoCor`: corestriction in degree
  `-2` is the map induced on abelianizations.

## References

* J.-P. Serre, *Local Fields*, Chapter VII, §8 and Chapter XI, §3.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
-/

public noncomputable section

universe u

open CategoryTheory Rep Finsupp

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Restriction

variable (S : Subgroup G) (A : Rep k G)

attribute [local instance] Subgroup.fintypeOfFinite

/-- Restriction in degree `-2` is the homological transfer through the comparison with `H₁`. -/
private theorem HNegTwoRes_comp_isoGroupHomology_hom :
    HNegTwoRes A S ≫ (_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app (res S.subtype A) =
      (_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app A ≫
        TauCeti.groupHomology.transfer A S 1 :=
  (Iso.eq_comp_inv ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).app _)).1
    ((HNegTwoRes_def _ _).trans (Category.assoc _ _ _).symm)

/-- Elementwise form of `HNegTwoRes_comp_isoGroupHomology_hom`, on the Tate class of `y`. -/
private theorem isoGroupHomology_hom_HNegTwoRes_inv (y : groupHomology A 1) :
    (_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app (res S.subtype A)
        (HNegTwoRes A S ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).inv.app A y)) =
      TauCeti.groupHomology.transfer A S 1 y := by
  have h1 := ConcreteCategory.congr_hom (HNegTwoRes_comp_isoGroupHomology_hom S A)
    ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).inv.app A y)
  rw [ModuleCat.comp_apply] at h1
  rw [h1]
  -- The composite on the right passes through `groupHomology.functor`, not `groupHomology`, so it
  -- is evaluated as a term rather than by `ModuleCat.comp_apply`.
  exact congrArg (TauCeti.groupHomology.transfer A S 1)
    (((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).app _).inv_hom_id_apply y)

/-- **Restriction in Tate degree `-2` is the Verlagerung.** For a subgroup `S` of a finite group
`G` and trivial coefficients `A`, restriction `Ĥ⁻²(G, A) ⟶ Ĥ⁻²(S, A)` becomes
`V ⊗ id : Gᵃᵇ ⊗ A → Sᵃᵇ ⊗ A` under the identifications `Ĥ⁻² ≃ (-)ᵃᵇ ⊗ A`, where `V` is the
group-theoretic transfer. -/
@[simp]
theorem HNegTwoAddEquivTensorOfIsTrivial_HNegTwoRes [A.IsTrivial] (x : tateCohomology A (-2)) :
    HNegTwoAddEquivTensorOfIsTrivial (res S.subtype A) (HNegTwoRes A S x) =
      LinearMap.rTensor A (AddMonoidHom.toIntLinearMap
        (Abelianization.lift (Abelianization.of : S →* Abelianization S).transfer).toAdditive)
        (HNegTwoAddEquivTensorOfIsTrivial A x) := by
  obtain ⟨t, rfl⟩ := (HNegTwoAddEquivTensorOfIsTrivial A).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul y a =>
    obtain ⟨g, rfl⟩ : ∃ g : G, Additive.ofMul (Abelianization.of g) = y :=
      QuotientGroup.mk'_surjective _ y.toMul
    obtain ⟨s, hs⟩ : ∃ s : S, Abelianization.of s =
        (Abelianization.of : S →* Abelianization S).transfer g :=
      QuotientGroup.mk'_surjective _ _
    rw [LinearMap.rTensor_tmul, AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply,
      toMul_ofMul, Abelianization.lift_apply_of, ← hs, ← AddEquiv.eq_symm_apply,
      HNegTwoAddEquivTensorOfIsTrivial_symm_tmul, HNegTwoAddEquivTensorOfIsTrivial_symm_tmul]
    apply (ModuleCat.mono_iff_injective ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app
      (res S.subtype A))).1 inferInstance
    rw [isoGroupHomology_hom_HNegTwoRes_inv, ← groupHomology.mkH1OfIsTrivial_apply,
      TauCeti.groupHomology.transfer_mkH1OfIsTrivial, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
      Abelianization.lift_apply_of, ← hs, groupHomology.mkH1OfIsTrivial_apply]
    exact (((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).app _).inv_hom_id_apply _).symm
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]

end Restriction

/-- **Corestriction in Tate degree `-2` is the map induced on abelianizations.** For a
homomorphism `f : H →* G` of finite groups and trivial coefficients `A`, corestriction
`Ĥ⁻²(H, A) ⟶ Ĥ⁻²(G, A)` becomes `Abelianization.map f ⊗ id : Hᵃᵇ ⊗ A → Gᵃᵇ ⊗ A` under the
identifications `Ĥ⁻² ≃ (-)ᵃᵇ ⊗ A`. -/
@[simp]
theorem HNegTwoAddEquivTensorOfIsTrivial_HNegTwoCor {H : Type u} [Group H] [Fintype H]
    (A : Rep k G) [A.IsTrivial] (f : H →* G) (y : tateCohomology (res f A) (-2)) :
    HNegTwoAddEquivTensorOfIsTrivial A (HNegTwoCor A f y) =
      LinearMap.rTensor A (AddMonoidHom.toIntLinearMap (Abelianization.map f).toAdditive)
        (HNegTwoAddEquivTensorOfIsTrivial (res f A) y) := by
  obtain ⟨t, rfl⟩ := (HNegTwoAddEquivTensorOfIsTrivial (res f A)).symm.surjective y
  rw [AddEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
    obtain ⟨h, rfl⟩ : ∃ h : H, Additive.ofMul (Abelianization.of h) = x :=
      QuotientGroup.mk'_surjective _ x.toMul
    rw [LinearMap.rTensor_tmul, AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply,
      toMul_ofMul, Abelianization.map_of, ← AddEquiv.eq_symm_apply,
      HNegTwoAddEquivTensorOfIsTrivial_symm_tmul, HNegTwoAddEquivTensorOfIsTrivial_symm_tmul]
    apply (ModuleCat.mono_iff_injective ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app
      A)).1 inferInstance
    have e₁ := ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).app (res f A)).inv_hom_id_apply
      (groupHomology.H1π (res f A)
        ((groupHomology.cycles₁IsoOfIsTrivial (res f A)).inv (single h a)))
    have e₂ := ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).app A).inv_hom_id_apply
      (groupHomology.H1π A ((groupHomology.cycles₁IsoOfIsTrivial A).inv (single (f h) a)))
    rw [Iso.app_hom, Iso.app_inv] at e₁ e₂
    rw [HNegTwoCor_comp_isoGroupHomology_hom_apply, e₁, e₂]
    -- As in the restriction case, the map on `H₁` is typed through `groupHomology.functor`, so the
    -- remaining equation is reached as a term.
    refine (TauCeti.groupHomology.map_mkH1OfIsTrivial f (𝟙 (res f A)) (.ofMul (.of h)) a).trans ?_
    rw [MonoidHom.toAdditive_apply_apply, toMul_ofMul, Abelianization.map_of, Rep.hom_id,
      Representation.IntertwiningMap.id_apply, groupHomology.mkH1OfIsTrivial_apply]
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]

end TauCeti.TateCohomology
