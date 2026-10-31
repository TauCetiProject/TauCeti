/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product

/-!
# Products of diagonalizable groups

The coordinate Hopf algebra of `D(G × H)` is the tensor product of the coordinate Hopf
algebras of `D(G)` and `D(H)`. This bundles the group-algebra product equivalence in the
finite-type category, for the ReductiveGroups roadmap Layer 4 target
"Diagonalizable groups and groups of multiplicative type".
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

/-- A character of the product maps to the pure tensor of its two characters. -/
@[simp]
theorem productCoordinateRingIso_hom_single (R : Type u) [CommRing R]
    (G H : FGCommGrpCat.{v}) (g : G) (h : H) :
    FiniteTypeCommHopfAlgCat.toBialgHom (productCoordinateRingIso R G H).hom
        (_root_.MonoidAlgebra.single (g, h) 1) =
      _root_.MonoidAlgebra.single g 1 ⊗ₜ[R] _root_.MonoidAlgebra.single h 1 :=
  MonoidAlgebra.prodTensorBialgEquiv_single R g h

end TauCeti.DiagonalizableGroup
