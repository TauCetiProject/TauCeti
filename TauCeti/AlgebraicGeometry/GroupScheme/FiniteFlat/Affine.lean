/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.FiniteFlat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.CartierDuality.FiniteLocallyFree

/-!
# Finite locally free group schemes over an affine base

A finite scheme over an affine scheme is affine. Consequently the category
`FiniteFlatCommGroupScheme (Spec R)` is equivalent to
`FiniteLocallyFreeCommAffineGroupSchemeCat R`: the two descriptions retain the same scheme,
structure morphism, group law and homomorphisms. This comparison allows the coordinate-Hopf-algebra
and Cartier-duality constructions to be used with the carrier defined over arbitrary schemes.

The functors `FiniteFlatCommGroupScheme.toAffine` and
`FiniteFlatCommGroupScheme.fromAffine` change only the bundling. Their composites with the
forgetful functors to group objects are identified by natural isomorphisms. In particular the
comparison does not choose an isomorphism with a spectrum or a presentation of a coordinate ring.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.12.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

open CategoryTheory AlgebraicGeometry

open scoped MonObj GrpObj

universe u

namespace TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme

variable (R : CommRingCat.{u})

/-- Regard a finite locally free commutative group scheme over an affine base as an object of
the affine category. Finiteness of its structure morphism supplies affineness of its carrier.
The object map is exposed so homomorphisms can be identified without dependent transports. -/
@[expose, implicit_reducible]
noncomputable def toAffine :
    FiniteFlatCommGroupScheme (Spec R) ⥤ FiniteLocallyFreeCommAffineGroupSchemeCat R where
  obj G := ⟨⟨Grp.mk G.toOver,
    (affineGroupSchemeProperty_iff _).mpr (isAffine_of_isAffineHom G.structureMap)⟩,
    (finiteLocallyFreeCommAffineGroupSchemeProperty_iff _ _).mpr
      ⟨G.finite, G.flat, G.locallyOfFinitePresentation, G.comm⟩⟩
  map f := ⟨⟨f.hom⟩⟩

/-- Affine rebundling retains the underlying group object. -/
@[simp]
theorem toAffine_obj_obj_obj (G : FiniteFlatCommGroupScheme (Spec R)) :
    ((toAffine R).obj G).obj.obj = Grp.mk G.toOver :=
  (rfl)

/-- Affine rebundling retains the structure morphism. -/
@[simp]
theorem toAffine_obj_obj_obj_X_hom (G : FiniteFlatCommGroupScheme (Spec R)) :
    ((toAffine R).obj G).obj.obj.X.hom = G.structureMap :=
  (rfl)

/-- Affine rebundling retains the unit section. -/
@[simp]
theorem toAffine_obj_one (G : FiniteFlatCommGroupScheme (Spec R)) :
    η[((toAffine R).obj G).obj.obj.X] = η[G.toOver] :=
  (rfl)

/-- Affine rebundling retains multiplication. -/
@[simp]
theorem toAffine_obj_mul (G : FiniteFlatCommGroupScheme (Spec R)) :
    μ[((toAffine R).obj G).obj.obj.X] = μ[G.toOver] :=
  (rfl)

/-- Affine rebundling retains inversion. -/
@[simp]
theorem toAffine_obj_inv (G : FiniteFlatCommGroupScheme (Spec R)) :
    ι[((toAffine R).obj G).obj.obj.X] = ι[G.toOver] :=
  (rfl)

/-- Affine rebundling retains the underlying homomorphism. -/
@[simp]
theorem toAffine_map_hom_hom {G H : FiniteFlatCommGroupScheme (Spec R)} (f : G ⟶ H) :
    ((toAffine R).map f).hom.hom = f.hom :=
  (rfl)

/-- Regard a finite locally free commutative affine group scheme as a finite locally free
commutative group scheme over its base spectrum, retaining its underlying group object.
The object map is exposed so structure maps and homomorphisms need no dependent transports. -/
@[expose, implicit_reducible]
noncomputable def fromAffine :
    FiniteLocallyFreeCommAffineGroupSchemeCat R ⥤ FiniteFlatCommGroupScheme (Spec R) where
  obj G :=
    { carrier := G.obj.obj.X.left
      structureMap := G.obj.obj.X.hom
      grp := inferInstanceAs (GrpObj G.obj.obj.X)
      comm := inferInstanceAs (IsCommMonObj G.obj.obj.X)
      finite := inferInstance
      flat := inferInstance
      locallyOfFinitePresentation := inferInstance }
  map f := homMk f.hom.hom

/-- Forgetting the affine bundling retains the carrier scheme. -/
@[simp]
theorem fromAffine_obj_carrier (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    ((fromAffine R).obj G).carrier = G.obj.obj.X.left :=
  (rfl)

/-- Forgetting the affine bundling retains the structure morphism. -/
@[simp]
theorem fromAffine_obj_structureMap (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    ((fromAffine R).obj G).structureMap = G.obj.obj.X.hom :=
  (rfl)

/-- Forgetting the affine bundling retains the scheme over the base. -/
theorem fromAffine_obj_toOver (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    ((fromAffine R).obj G).toOver = G.obj.obj.X :=
  (rfl)

/-- Forgetting the affine bundling retains the group object. -/
@[simp]
theorem grpMk_fromAffine_obj (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    Grp.mk ((fromAffine R).obj G).toOver = G.obj.obj :=
  (rfl)

/-- Forgetting the affine bundling retains the unit section. -/
@[simp]
theorem fromAffine_obj_one (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    η[((fromAffine R).obj G).toOver] = η[G.obj.obj.X] :=
  (rfl)

/-- Forgetting the affine bundling retains the multiplication. -/
@[simp]
theorem fromAffine_obj_mul (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    μ[((fromAffine R).obj G).toOver] = μ[G.obj.obj.X] :=
  (rfl)

/-- Forgetting the affine bundling retains inversion. -/
@[simp]
theorem fromAffine_obj_inv (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    ι[((fromAffine R).obj G).toOver] = ι[G.obj.obj.X] :=
  (rfl)

/-- Forgetting the affine bundling after affine rebundling recovers the original group scheme. -/
@[simp]
theorem fromAffine_obj_toAffine_obj (G : FiniteFlatCommGroupScheme (Spec R)) :
    (fromAffine R).obj ((toAffine R).obj G) = G :=
  (rfl)

/-- Affine rebundling after forgetting the bundling recovers the original affine group scheme. -/
@[simp]
theorem toAffine_obj_fromAffine_obj (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    (toAffine R).obj ((fromAffine R).obj G) = G :=
  (rfl)

/-- Forgetting the affine bundling retains the underlying homomorphism. -/
@[simp]
theorem fromAffine_map_hom {G H : FiniteLocallyFreeCommAffineGroupSchemeCat R} (f : G ⟶ H) :
    ((fromAffine R).map f).hom = f.hom.hom :=
  (rfl)

/-- Forgetting after affine rebundling recovers the original homomorphism. -/
@[simp]
theorem fromAffine_map_toAffine_map {G H : FiniteFlatCommGroupScheme (Spec R)} (f : G ⟶ H) :
    (fromAffine R).map ((toAffine R).map f) = f :=
  (rfl)

/-- Affine rebundling after forgetting recovers the original affine homomorphism. -/
@[simp]
theorem toAffine_map_fromAffine_map {G H : FiniteLocallyFreeCommAffineGroupSchemeCat R}
    (f : G ⟶ H) : (toAffine R).map ((fromAffine R).map f) = f :=
  (rfl)

/-- Rebundling in the affine category leaves the underlying group scheme unchanged. -/
noncomputable def toAffineCompιIso :
    toAffine R ⋙ (finiteLocallyFreeCommAffineGroupSchemeProperty R).ι ⋙
        (affineGroupSchemeProperty R).ι ≅ toGrp (Spec R) :=
  Iso.refl _

/-- Forgetting the affine bundling leaves the underlying group scheme unchanged. -/
noncomputable def fromAffineCompToGrpIso :
    fromAffine R ⋙ toGrp (Spec R) ≅
      (finiteLocallyFreeCommAffineGroupSchemeProperty R).ι ⋙ (affineGroupSchemeProperty R).ι :=
  Iso.refl _

/-- The forward forgetful comparison has identity components. -/
@[simp]
theorem toAffineCompιIso_hom_app (G : FiniteFlatCommGroupScheme (Spec R)) :
    (toAffineCompιIso R).hom.app G = 𝟙 (Grp.mk G.toOver) :=
  (rfl)

/-- The inverse forward forgetful comparison has identity components. -/
@[simp]
theorem toAffineCompιIso_inv_app (G : FiniteFlatCommGroupScheme (Spec R)) :
    (toAffineCompιIso R).inv.app G = 𝟙 (Grp.mk G.toOver) :=
  (rfl)

/-- The backward forgetful comparison has identity components. -/
@[simp]
theorem fromAffineCompToGrpIso_hom_app (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    (fromAffineCompToGrpIso R).hom.app G = 𝟙 G.obj.obj :=
  (rfl)

/-- The inverse backward forgetful comparison has identity components. -/
@[simp]
theorem fromAffineCompToGrpIso_inv_app (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    (fromAffineCompToGrpIso R).inv.app G = 𝟙 G.obj.obj :=
  (rfl)

/-- Finite locally free commutative group schemes over an affine base are equivalent to the
finite locally free commutative affine group schemes over the same ring. Both directions keep
the underlying group scheme and every homomorphism unchanged. The directions are exposed so
unit and counit components can be stated as identities without dependent transports. -/
@[expose, implicit_reducible]
noncomputable def affineEquivalence :
    FiniteFlatCommGroupScheme (Spec R) ≌ FiniteLocallyFreeCommAffineGroupSchemeCat R where
  functor := toAffine R
  inverse := fromAffine R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance : (toAffine R).IsEquivalence := (affineEquivalence R).isEquivalence_functor

instance : (fromAffine R).IsEquivalence := (affineEquivalence R).isEquivalence_inverse

/-- The affine equivalence sends a group scheme to its affine bundling. -/
@[simp]
theorem affineEquivalence_functor : (affineEquivalence R).functor = toAffine R :=
  (rfl)

/-- The inverse affine equivalence forgets the affine bundling. -/
@[simp]
theorem affineEquivalence_inverse : (affineEquivalence R).inverse = fromAffine R :=
  (rfl)

/-- The unit of the affine equivalence is the identity on underlying group objects. -/
@[simp]
theorem affineEquivalence_unitIso_hom_app (G : FiniteFlatCommGroupScheme (Spec R)) :
    (affineEquivalence R).unitIso.hom.app G = 𝟙 G :=
  (rfl)

/-- The inverse unit of the affine equivalence is the identity on underlying group objects. -/
@[simp]
theorem affineEquivalence_unitIso_inv_app (G : FiniteFlatCommGroupScheme (Spec R)) :
    (affineEquivalence R).unitIso.inv.app G = 𝟙 G :=
  (rfl)

/-- The counit of the affine equivalence is the identity. -/
@[simp]
theorem affineEquivalence_counitIso_hom_app
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    (affineEquivalence R).counitIso.hom.app G = 𝟙 G :=
  (rfl)

/-- The inverse counit of the affine equivalence is the identity. -/
@[simp]
theorem affineEquivalence_counitIso_inv_app
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat R) :
    (affineEquivalence R).counitIso.inv.app G = 𝟙 G :=
  (rfl)

end TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme
