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

universe u

namespace TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme

variable (R : CommRingCat.{u})

/-- Regard a finite locally free commutative group scheme over an affine base as an object of
the affine category. Finiteness of its structure morphism supplies affineness of its carrier.
The object map is exposed so homomorphisms can be identified without dependent transports. -/
@[expose]
noncomputable def toAffine :
    FiniteFlatCommGroupScheme (Spec R) ⥤ FiniteLocallyFreeCommAffineGroupSchemeCat R where
  obj G := ⟨⟨Grp.mk G.toOver,
    (affineGroupSchemeProperty_iff _).mpr (isAffine_of_isAffineHom G.structureMap)⟩,
    (finiteLocallyFreeCommAffineGroupSchemeProperty_iff _ _).mpr
      ⟨G.finite, G.flat, G.locallyOfFinitePresentation, G.comm⟩⟩
  map f := ⟨⟨f⟩⟩

/-- Affine rebundling retains the underlying group object. -/
@[simp]
theorem toAffine_obj_obj_obj (G : FiniteFlatCommGroupScheme (Spec R)) :
    ((toAffine R).obj G).obj.obj = Grp.mk G.toOver :=
  (rfl)

/-- Affine rebundling retains the underlying homomorphism. -/
@[simp]
theorem toAffine_map_hom_hom {G H : FiniteFlatCommGroupScheme (Spec R)} (f : G ⟶ H) :
    ((toAffine R).map f).hom.hom = f :=
  (rfl)

/-- Regard a finite locally free commutative affine group scheme as a finite locally free
commutative group scheme over its base spectrum, retaining its underlying group object.
The object map is exposed so structure maps and homomorphisms need no dependent transports. -/
@[expose]
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
  map f := f.hom.hom

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

/-- Forgetting the affine bundling retains the underlying homomorphism. -/
@[simp]
theorem fromAffine_map {G H : FiniteLocallyFreeCommAffineGroupSchemeCat R} (f : G ⟶ H) :
    (fromAffine R).map f = f.hom.hom :=
  (rfl)

/-- Rebundling in the affine category leaves the underlying group scheme unchanged. -/
noncomputable def toAffineCompForgetIso :
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
theorem toAffineCompForgetIso_hom_app (G : FiniteFlatCommGroupScheme (Spec R)) :
    (toAffineCompForgetIso R).hom.app G = 𝟙 (Grp.mk G.toOver) :=
  (rfl)

/-- The inverse forward forgetful comparison has identity components. -/
@[simp]
theorem toAffineCompForgetIso_inv_app (G : FiniteFlatCommGroupScheme (Spec R)) :
    (toAffineCompForgetIso R).inv.app G = 𝟙 (Grp.mk G.toOver) :=
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
@[expose]
noncomputable def affineEquivalence :
    FiniteFlatCommGroupScheme (Spec R) ≌ FiniteLocallyFreeCommAffineGroupSchemeCat R :=
  CategoryTheory.Equivalence.mk (toAffine R) (fromAffine R)
    (NatIso.ofComponents (fun _ ↦ { hom := 𝟙 _, inv := 𝟙 _ }))
    (NatIso.ofComponents (fun _ ↦ { hom := ⟨⟨𝟙 _⟩⟩, inv := ⟨⟨𝟙 _⟩⟩ }))

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
    (affineEquivalence R).unitIso.hom.app G = 𝟙 G := by
  simp [affineEquivalence, CategoryTheory.Equivalence.mk,
    CategoryTheory.Equivalence.adjointifyη, NatIso.ofComponents, toAffine, fromAffine]
  rfl

/-- The inverse unit of the affine equivalence is the identity on underlying group objects. -/
@[simp]
theorem affineEquivalence_unitIso_inv_app (G : FiniteFlatCommGroupScheme (Spec R)) :
    (affineEquivalence R).unitIso.inv.app G = 𝟙 G := by
  dsimp [affineEquivalence, CategoryTheory.Equivalence.mk,
    CategoryTheory.Equivalence.adjointifyη, NatIso.ofComponents, toAffine, fromAffine]
  simp only [Category.comp_id, Category.id_comp]
  exact Category.comp_id (𝟙 (Grp.mk G.toOver))

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
