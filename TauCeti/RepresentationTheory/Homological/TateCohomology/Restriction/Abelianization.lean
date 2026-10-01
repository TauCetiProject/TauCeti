/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Basic
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Abelianization
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Basic

/-!
# Restriction and corestriction in Tate degree `-2` on the abelianization

For a finite group `G` and trivial coefficients `A`, degree `-2` Tate cohomology is
`H_Tate⁻²(G, A) ≃ Gᵃᵇ ⊗ A` (`TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial`). This file
identifies the two change-of-group maps in this degree under that identification:

* restriction to a subgroup `S ≤ G`, `H_Tate⁻²(G, A) ⟶ H_Tate⁻²(S, A)`, is the
  group-theoretic transfer (Verlagerung) `Gᵃᵇ → Sᵃᵇ`, tensored with `A`;
* corestriction along a homomorphism `f : H →* G`, `H_Tate⁻²(H, A) ⟶ H_Tate⁻²(G, A)`, is
  `Abelianization.map f`, tensored with `A`.

Together they make the identification `H_Tate⁻²(G, A) ≃ Gᵃᵇ ⊗ A` natural in the group: a
statement about restriction or corestriction in Tate degree `-2` can be transported to the
corresponding statement about the Verlagerung or `Abelianization.map`. For `A = ℤ`, these are the
compatibilities of the identification `H_Tate⁻²(G, ℤ) ≃ Gᵃᵇ` with restriction and corestriction
that the reciprocity isomorphism `Gᵃᵇ ≃ H_Tate⁰(G, C)` inherits.

## Main results

* `TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial_HNegTwoRes`: restriction in degree `-2`
  is the Verlagerung.
* `TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial_HNegTwoCor`: corestriction in degree
  `-2` is the map induced on abelianizations.
* `TauCeti.TateCohomology.HNegTwoAddEquivAbelianization_map`: with integral coefficients, Tate
  cohomology along an isomorphism of finite groups is, in degree `-2`, the induced isomorphism of
  abelianizations.

## References

* J.-P. Serre, *Local Fields*, Chapter VII, §8 and Chapter XI, §3.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
-/

public noncomputable section

universe u

open CategoryTheory Rep Finsupp
open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Restriction

variable (S : Subgroup G) (A : Rep k G)

attribute [local instance] Subgroup.fintypeOfFinite

/-- **Restriction in Tate degree `-2` is the Verlagerung.** For a subgroup `S` of a finite group
`G` and trivial coefficients `A`, restriction `H_Tate⁻²(G, A) ⟶ H_Tate⁻²(S, A)` becomes
`V ⊗ id : Gᵃᵇ ⊗ A → Sᵃᵇ ⊗ A` under the identifications `H_Tate⁻² ≃ (-)ᵃᵇ ⊗ A`, where `V` is the
group-theoretic transfer. -/
@[simp]
theorem HNegTwoAddEquivTensorOfIsTrivial_HNegTwoRes [A.IsTrivial] (x : tateCohomology A (-2)) :
    HNegTwoAddEquivTensorOfIsTrivial (res S.subtype A) (HNegTwoRes A S x) =
      LinearMap.rTensor A (AddMonoidHom.toIntLinearMap
        (Abelianization.lift (Abelianization.of : S →* Abelianization S).transfer).toAdditive)
        (HNegTwoAddEquivTensorOfIsTrivial A x) := by
  rw [HNegTwoAddEquivTensorOfIsTrivial_apply,
    HNegTwoAddEquivTensorOfIsTrivial_apply,
    HNegTwoRes_comp_isoGroupHomology_hom_apply]
  convert TauCeti.groupHomology.H1AddEquivOfIsTrivial_transfer S A
    ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app A x) using 1

end Restriction

/-- **Corestriction in Tate degree `-2` is the map induced on abelianizations.** For a
homomorphism `f : H →* G` of finite groups and trivial coefficients `A`, corestriction
`H_Tate⁻²(H, A) ⟶ H_Tate⁻²(G, A)` becomes `Abelianization.map f ⊗ id : Hᵃᵇ ⊗ A → Gᵃᵇ ⊗ A` under the
identifications `H_Tate⁻² ≃ (-)ᵃᵇ ⊗ A`. -/
@[simp]
theorem HNegTwoAddEquivTensorOfIsTrivial_HNegTwoCor {H : Type u} [Group H] [Fintype H]
    (A : Rep k G) [A.IsTrivial] (f : H →* G) (y : tateCohomology (res f A) (-2)) :
    HNegTwoAddEquivTensorOfIsTrivial A (HNegTwoCor A f y) =
      LinearMap.rTensor A (AddMonoidHom.toIntLinearMap (Abelianization.map f).toAdditive)
        (HNegTwoAddEquivTensorOfIsTrivial (res f A) y) := by
  rw [HNegTwoAddEquivTensorOfIsTrivial_apply,
    HNegTwoAddEquivTensorOfIsTrivial_apply,
    HNegTwoCor_comp_isoGroupHomology_hom_apply]
  convert TauCeti.groupHomology.H1AddEquivOfIsTrivial_map f (𝟙 (Rep.res f A))
    ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app (res f A) y) using 1
  rw [LinearMap.rTensor_def, Rep.hom_id, Representation.IntertwiningMap.toLinearMap_id]
  congr 1

section TrivialInt

variable {G : Type} [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- Under the integral degree-`-2` identification, restriction to a subgroup is the
group-theoretic transfer. -/
@[simp]
theorem HNegTwoAddEquivAbelianization_HNegTwoRes (S : Subgroup G)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    TensorProduct.rid ℤ (Additive (Abelianization S))
        (HNegTwoAddEquivTensorOfIsTrivial
          (Rep.res S.subtype (Rep.trivial ℤ G ℤ))
          (HNegTwoRes (Rep.trivial ℤ G ℤ) S x)) =
      (Abelianization.lift
        (Abelianization.of : S →* Abelianization S).transfer).toAdditive
        (HNegTwoAddEquivAbelianization x) := by
  rw [HNegTwoAddEquivTensorOfIsTrivial_HNegTwoRes,
    TauCeti.tensorProduct_rid_rTensor_apply, HNegTwoAddEquivAbelianization_apply,
    AddMonoidHom.coe_toIntLinearMap]

/-- Under the integral degree-`-2` identification, corestriction along a homomorphism is the
map that it induces on abelianizations. -/
@[simp]
theorem HNegTwoAddEquivAbelianization_HNegTwoCor {H : Type} [Group H] [Fintype H]
    (f : H →* G)
    (y : tateCohomology (Rep.res f (Rep.trivial ℤ G ℤ)) (-2)) :
    HNegTwoAddEquivAbelianization
        (HNegTwoCor (Rep.trivial ℤ G ℤ) f y) =
      (Abelianization.map f).toAdditive
        (TensorProduct.rid ℤ (Additive (Abelianization H))
          (HNegTwoAddEquivTensorOfIsTrivial
            (Rep.res f (Rep.trivial ℤ G ℤ)) y)) := by
  rw [HNegTwoAddEquivAbelianization_apply,
    HNegTwoAddEquivTensorOfIsTrivial_HNegTwoCor,
    TauCeti.tensorProduct_rid_rTensor_apply, AddMonoidHom.coe_toIntLinearMap]

/-- **The integral degree-`-2` identification is natural along isomorphisms of groups**: Tate
cohomology along an isomorphism `e : G ≃* H` of finite groups, with integral coefficients, is the
isomorphism `Gᵃᵇ ≃ Hᵃᵇ` induced by `e` in degree `-2`. -/
theorem HNegTwoAddEquivAbelianization_map {H : Type} [Group H] [Fintype H] (e : G ≃* H)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    HNegTwoAddEquivAbelianization
        (map (MonoidHom.isIntertwiningMap_trivial (e : G →* H)) (-2) x) =
      e.abelianizationCongr.toAdditive (HNegTwoAddEquivAbelianization x) := by
  -- In degree `-2` the pair acts on first homology as the change-of-group map along `e`.
  have hm : (_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app (Rep.trivial ℤ H ℤ)
      (map (MonoidHom.isIntertwiningMap_trivial (e : G →* H)) (-2) x) =
      groupHomology.map (e : G →* H)
        (Representation.IsIntertwiningMap.toRes
          (MonoidHom.isIntertwiningMap_trivial (e : G →* H))) 1
        ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app (Rep.trivial ℤ G ℤ) x) :=
    ConcreteCategory.congr_hom
      (map_comp_isoGroupHomology_hom
        (MonoidHom.isIntertwiningMap_trivial (e : G →* H)) (-2) 1 rfl) x
  rw [HNegTwoAddEquivAbelianization_apply, HNegTwoAddEquivAbelianization_apply,
    HNegTwoAddEquivTensorOfIsTrivial_apply, HNegTwoAddEquivTensorOfIsTrivial_apply, hm]
  -- On first homology with trivial coefficients, the change of group along `e` is
  -- `Abelianization.map e` tensored with the identity of `ℤ`.
  have h1 := TauCeti.groupHomology.H1AddEquivOfIsTrivial_map (e : G →* H)
    (Representation.IsIntertwiningMap.toRes (MonoidHom.isIntertwiningMap_trivial (e : G →* H)))
    ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app (Rep.trivial ℤ G ℤ) x :
      groupHomology.H1 (Rep.trivial ℤ G ℤ))
  refine (congrArg (TensorProduct.rid ℤ (Additive (Abelianization H))) h1).trans ?_
  simp only [Representation.IsIntertwiningMap.toRes_hom_toLinearMap, LinearEquiv.refl_toLinearMap,
    LinearMap.restrictScalars_self]
  rw [← LinearMap.rTensor_def, TauCeti.tensorProduct_rid_rTensor_apply]
  -- `MulEquiv.abelianizationCongr e` is `Abelianization.map e` on underlying functions.
  rfl

end TrivialInt

end TauCeti.TateCohomology
