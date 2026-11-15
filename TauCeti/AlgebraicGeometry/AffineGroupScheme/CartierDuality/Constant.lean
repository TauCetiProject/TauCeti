/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Scheme
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.CartierDuality.FiniteLocallyFree

/-!
# Cartier duals of finite constant and diagonalizable groups

For a finite commutative group `G` over a commutative ring `R`, the constant group and the
diagonalizable group `D(G)` are Cartier dual. The constant coordinate algebra is already the
finite convolution dual of `R[G]`; double-dual evaluation therefore supplies the comparison in
the other direction. These identifications concern the existing group schemes, with their group
laws, and hold without invertibility assumptions on the order of `G`.

For `G = Multiplicative (ZMod N)`, with positive `N`, `D(G)` is the group scheme `μ_N`.
Thus the two isomorphisms specialize to the duality of the constant cyclic group and `μ_N`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* SGA 3, Exposé VIIA, §3.3.

The coordinate construction is `ConstantGroup.coordinateRing`; biduality is
`ConvolutionDual.evalBialgEquiv`. The group-scheme comparisons use the transported
`FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDuality` and the existing constant and
diagonalizable `groupScheme` constructions.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

open finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

variable (R : Type u) [CommRing R]

namespace DiagonalizableGroup

variable (G : FGCommGrpCat.{u}) [Finite G]

/-- The finite diagonalizable group scheme bundled as a finite locally free commutative affine
group scheme. -/
noncomputable def finiteLocallyFreeGroupScheme :
    FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  ⟨⟨groupScheme R G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩, by
    let H := FiniteLocallyFreeBicommutativeHopfAlgCat.of R (MonoidAlgebra R G)
    let e :
        ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor.obj (op H)).obj ≅
          ⟨groupScheme R G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩ :=
      (affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((functorCompιIso R).app (op H) ≪≫ eqToIso (groupScheme_def R G).symm)
    exact (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso
      e ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).functor.obj (op H)).property⟩

/-- Forgetting finite local freeness recovers the existing diagonalizable group scheme. -/
@[simp]
theorem finiteLocallyFreeGroupScheme_obj_obj (G : FGCommGrpCat.{u}) [Finite G] :
    (finiteLocallyFreeGroupScheme R G).obj.obj = groupScheme R G :=
  (rfl)

/-- The Hopf--spectrum anti-equivalence sends the group algebra to the finite diagonalizable
group scheme. -/
noncomputable def finiteLocallyFreeGroupSchemeIso :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
      R).functor.obj
        (op (FiniteLocallyFreeBicommutativeHopfAlgCat.of R (MonoidAlgebra R G))) ≅
      finiteLocallyFreeGroupScheme R G :=
  functorObjIso R _ ≪≫
    (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
        (eqToIso (groupScheme_def R G).symm))

end DiagonalizableGroup

namespace ConstantGroup

variable (G : Type u) [CommGroup G] [Finite G]

/-- The finite constant group scheme bundled as a finite locally free commutative affine
group scheme. -/
noncomputable def finiteLocallyFreeGroupScheme :
    FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  ⟨⟨groupScheme R G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩, by
    let H := FiniteLocallyFreeBicommutativeHopfAlgCat.of R (coordinateRing R G)
    let e :
        ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor.obj (op H)).obj ≅
          ⟨groupScheme R G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩ :=
      (affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((functorCompιIso R).app (op H) ≪≫ eqToIso (groupScheme_def R G).symm)
    exact (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso
      e ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).functor.obj (op H)).property⟩

/-- Forgetting finite local freeness recovers the existing constant group scheme. -/
@[simp]
theorem finiteLocallyFreeGroupScheme_obj_obj :
    (finiteLocallyFreeGroupScheme R G).obj.obj = groupScheme R G :=
  (rfl)

/-- The Hopf--spectrum anti-equivalence sends the finite dual of the group algebra to the
finite constant group scheme. -/
noncomputable def finiteLocallyFreeGroupSchemeIso :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
      R).functor.obj
        (op (FiniteLocallyFreeBicommutativeHopfAlgCat.of R (coordinateRing R G))) ≅
      finiteLocallyFreeGroupScheme R G :=
  functorObjIso R _ ≪≫
    (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
        (eqToIso (groupScheme_def R G).symm))

end ConstantGroup

namespace DiagonalizableGroup

variable (G : FGCommGrpCat.{u}) [Finite G]

/-- The Cartier dual of a finite diagonalizable group is its constant character group. -/
noncomputable def cartierDualIso :
    FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDual R
        (finiteLocallyFreeGroupScheme R G) ≅
      ConstantGroup.finiteLocallyFreeGroupScheme R G :=
  (FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualFunctor R).mapIso
      (finiteLocallyFreeGroupSchemeIso R G).op ≪≫
    FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualHopfSpecIso R
      (FiniteLocallyFreeBicommutativeHopfAlgCat.of R (MonoidAlgebra R G)) ≪≫
    ConstantGroup.finiteLocallyFreeGroupSchemeIso R G

/-- The duality comparison for a diagonalizable group is finite dualization followed by the
constant-group coordinate presentation. This equation characterizes the comparison without
unfolding its definition. -/
theorem cartierDualIso_hom :
    (cartierDualIso R G).hom =
      (FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualFunctor R).map
          (finiteLocallyFreeGroupSchemeIso R G).op.hom ≫
        (FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualHopfSpecIso R
          (FiniteLocallyFreeBicommutativeHopfAlgCat.of R (MonoidAlgebra R G))).hom ≫
        (ConstantGroup.finiteLocallyFreeGroupSchemeIso R G).hom :=
  (rfl)

end DiagonalizableGroup

namespace ConstantGroup

variable (G : FGCommGrpCat.{u}) [Finite G]

/-- The Cartier dual of a finite commutative constant group is the diagonalizable group with
that character group. -/
noncomputable def cartierDualIso :
    FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDual R
        (finiteLocallyFreeGroupScheme R G) ≅
      DiagonalizableGroup.finiteLocallyFreeGroupScheme R G :=
  (FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualFunctor R).mapIso
      (finiteLocallyFreeGroupSchemeIso R G).op ≪≫
    FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualHopfSpecIso R
      (FiniteLocallyFreeBicommutativeHopfAlgCat.of R (coordinateRing R G)) ≪≫
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
      R).functor.mapIso
        (FiniteLocallyFreeBicommutativeHopfAlgCat.evalIso
          (FiniteLocallyFreeBicommutativeHopfAlgCat.of R (MonoidAlgebra R G))).op ≪≫
    DiagonalizableGroup.finiteLocallyFreeGroupSchemeIso R G

/-- The duality comparison for a constant group is induced by double-dual evaluation on its
group algebra, through the Hopf--spectrum anti-equivalence. -/
theorem cartierDualIso_hom :
    (cartierDualIso R G).hom =
      (FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualFunctor R).map
          (finiteLocallyFreeGroupSchemeIso R G).op.hom ≫
        (FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualHopfSpecIso R
          (FiniteLocallyFreeBicommutativeHopfAlgCat.of R (coordinateRing R G))).hom ≫
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor.map
            (FiniteLocallyFreeBicommutativeHopfAlgCat.evalIso
              (FiniteLocallyFreeBicommutativeHopfAlgCat.of R (MonoidAlgebra R G))).op.hom ≫
        (DiagonalizableGroup.finiteLocallyFreeGroupSchemeIso R G).hom :=
  (rfl)

end ConstantGroup

end TauCeti
