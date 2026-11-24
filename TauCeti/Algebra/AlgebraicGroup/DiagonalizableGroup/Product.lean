/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product

/-!
# Products of diagonalizable groups

The coordinate Hopf algebra of `D(G × H)` is the tensor product of the coordinate Hopf
algebras of `D(G)` and `D(H)`. This bundles the group-algebra product equivalence
`TauCeti.MonoidAlgebra.prodTensorBialgEquiv` in the finite-type category. Over a field, it
follows that a product of diagonalizable groups is diagonalizable.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.DiagonalizableGroup

universe u v

/-- The coordinate Hopf algebra of the product character group is the tensor product
of the two coordinate Hopf algebras. -/
noncomputable def productCoordinateRingIso (R : Type u) [CommRing R]
    (G H : FGCommGrpCat.{v}) :
    coordinateRing R (FGCommGrpCat.of (G × H)) ≅
      FiniteTypeCommHopfAlgCat.tensorProduct (coordinateRing R G) (coordinateRing R H) :=
  ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    MonoidAlgebra.prodTensorBialgEquiv R

/-- A scalar multiple of a character of the product maps to the pure tensor of its two
characters, the scalar being carried by the second factor. -/
@[simp]
theorem productCoordinateRingIso_hom_single (R : Type u) [CommRing R]
    (G H : FGCommGrpCat.{v}) (p : G × H) (r : R) :
    FiniteTypeCommHopfAlgCat.toBialgHom (productCoordinateRingIso R G H).hom
        (_root_.MonoidAlgebra.single p r) =
      _root_.MonoidAlgebra.single p.1 1 ⊗ₜ[R] _root_.MonoidAlgebra.single p.2 r :=
  MonoidAlgebra.prodTensorBialgEquiv_single R p r

/-- A pure tensor of scalar multiples of two characters maps back to the corresponding scalar
multiple of the character of the product. -/
@[simp]
theorem productCoordinateRingIso_inv_single_tmul_single (R : Type u) [CommRing R]
    (G H : FGCommGrpCat.{v}) (g : G) (h : H) (r s : R) :
    FiniteTypeCommHopfAlgCat.toBialgHom (productCoordinateRingIso R G H).inv
        (_root_.MonoidAlgebra.single g r ⊗ₜ[R] _root_.MonoidAlgebra.single h s) =
      _root_.MonoidAlgebra.single (g, h) (r * s) :=
  MonoidAlgebra.prodTensorBialgEquiv_symm_single_tmul_single R g h r s

/-- The product isomorphism carries the coordinate map of the first inclusion of character
groups to the left coordinate inclusion. -/
@[reassoc]
theorem coordinateMap_inl_comp_productCoordinateRingIso_hom (R : Type u) [CommRing R]
    (G H : FGCommGrpCat.{v}) :
    coordinateMap R (FGCommGrpCat.ofHom (MonoidHom.inl G H)) ≫
        (productCoordinateRingIso R G H).hom =
      FiniteTypeCommHopfAlgCat.includeLeft (coordinateRing R G) (coordinateRing R H) := by
  apply FiniteTypeCommHopfAlgCat.hom_ext
  apply _root_.MonoidAlgebra.bialgHom_ext
  · intro g
    rw [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply, coordinateMap_single,
      FGCommGrpCat.hom_hom_ofHom, MonoidHom.inl_apply, productCoordinateRingIso_hom_single,
      FiniteTypeCommHopfAlgCat.includeLeft_apply, _root_.MonoidAlgebra.one_def]
  · exact Subsingleton.elim _ _

/-- The product isomorphism carries the coordinate map of the second inclusion of character
groups to the right coordinate inclusion. -/
@[reassoc]
theorem coordinateMap_inr_comp_productCoordinateRingIso_hom (R : Type u) [CommRing R]
    (G H : FGCommGrpCat.{v}) :
    coordinateMap R (FGCommGrpCat.ofHom (MonoidHom.inr G H)) ≫
        (productCoordinateRingIso R G H).hom =
      FiniteTypeCommHopfAlgCat.includeRight (coordinateRing R G) (coordinateRing R H) := by
  apply FiniteTypeCommHopfAlgCat.hom_ext
  apply _root_.MonoidAlgebra.bialgHom_ext
  · intro h
    rw [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply, coordinateMap_single,
      FGCommGrpCat.hom_hom_ofHom, MonoidHom.inr_apply, productCoordinateRingIso_hom_single,
      FiniteTypeCommHopfAlgCat.includeRight_apply, _root_.MonoidAlgebra.one_def]
  · exact Subsingleton.elim _ _

/-- Products of finite-type diagonalizable groups over a field are diagonalizable: the tensor
product of two finite-type commutative Hopf algebras spanned by their group-like elements is
spanned by its group-like elements. -/
theorem groupLikeSpannedProperty.tensorProduct (k : Type u) [Field k]
    (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : groupLikeSpannedProperty k H) (hK : groupLikeSpannedProperty k K) :
    groupLikeSpannedProperty k (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
  rw [← essImage_coordinateRingFunctor] at hH hK ⊢
  obtain ⟨G, ⟨e⟩⟩ := hH
  obtain ⟨G', ⟨f⟩⟩ := hK
  exact ⟨FGCommGrpCat.of (G × G'), ⟨productCoordinateRingIso k G G' ≪≫
    FiniteTypeCommHopfAlgCat.tensorProductCongr e f⟩⟩

end TauCeti.DiagonalizableGroup
