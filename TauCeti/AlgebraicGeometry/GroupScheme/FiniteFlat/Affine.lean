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
the affine category. Finiteness of its structure morphism supplies affineness of its carrier. -/
noncomputable def toAffine :
    FiniteFlatCommGroupScheme (Spec R) ⥤ FiniteLocallyFreeCommAffineGroupSchemeCat R where
  obj G := ⟨⟨Grp.mk G.toOver,
    (affineGroupSchemeProperty_iff _).mpr (isAffine_of_isAffineHom G.structureMap)⟩,
    (finiteLocallyFreeCommAffineGroupSchemeProperty_iff _ _).mpr
      ⟨G.finite, G.flat, G.locallyOfFinitePresentation, G.comm⟩⟩
  map f := ⟨⟨f⟩⟩

/-- Regard a finite locally free commutative affine group scheme as a finite locally free
commutative group scheme over its base spectrum, retaining its underlying group object. -/
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

/-- Finite locally free commutative group schemes over an affine base are equivalent to the
finite locally free commutative affine group schemes over the same ring. Both directions keep
the underlying group scheme and every homomorphism unchanged. -/
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

end TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme
