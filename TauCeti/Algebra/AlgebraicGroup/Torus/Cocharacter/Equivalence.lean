/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Cocharacter.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Equivalence
public import TauCeti.RepresentationTheory.GaloisLattice.Duality

/-!
# Classification of tori by cocharacter lattices

The cocharacter-lattice functor is naturally isomorphic to the integral dual of the
character-lattice functor. Over a perfect field it is therefore an equivalence: continuous
integral Galois lattices classify tori covariantly, or their coordinate Hopf algebras
contravariantly. The comparison of functors itself holds over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.
-/

public section

open CategoryTheory

namespace TauCeti.TorusCommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- The intrinsic cocharacter-dual comparison as an isomorphism of Galois representations. -/
private noncomputable def cocharacterRepresentationIsoDual (T : TorusCommHopfAlgCat k) :
    cocharacterLatticeRepresentation T ≅
      (CommHopfAlgCat.geometricCharacterRepresentation T.obj.obj).dual :=
  Rep.mkIso (Representation.Equiv.mk
    (MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toMultiplicativeTypeCommHopfAlgCat T)) fun σ ↦ by
    ext y x
    exact MultiplicativeTypeCommHopfAlgCat.cocharacterGaloisRepresentation_apply_apply
      (toMultiplicativeTypeCommHopfAlgCat T) σ y x)

/-- The cocharacter-dual comparison is natural in the underlying Galois representations. -/
private theorem cocharacterRepresentationIsoDual_naturality
    {S T : TorusCommHopfAlgCat k} (f : S ⟶ T) :
    cocharacterLatticeRepresentationMap f ≫ (cocharacterRepresentationIsoDual S).hom =
      (cocharacterRepresentationIsoDual T).hom ≫
        Rep.dualMap (CommHopfAlgCat.geometricCharacterRepresentationMap f.hom.hom) := by
  ext y x
  -- Express the bundled carriers as character and cocharacter modules so their
  -- evaluation lemmas apply.
  dsimp only [cocharacterLatticeRepresentation, CommHopfAlgCat.geometricCharacterRepresentation,
    Rep.ofMulDistribMulAction, Rep.of] at y x
  change (MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toMultiplicativeTypeCommHopfAlgCat S))
      ((cocharacterLatticeRepresentationMap f).hom y) x =
    (Rep.dualMap (CommHopfAlgCat.geometricCharacterRepresentationMap f.hom.hom)).hom
      ((MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
        (toMultiplicativeTypeCommHopfAlgCat T)) y) x
  erw [Rep.dualMap_hom_apply, cocharacterLatticeRepresentationMap_hom_apply,
    CommHopfAlgCat.geometricCharacterRepresentationMap_hom_apply]
  exact MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual_cocharacterMap_apply
    (toMultiplicativeTypeMap f) y x

/-- The cocharacter-lattice functor is the contragredient dual of the character-lattice functor.
This identifies the intrinsic geometric cocharacters with integral character functionals. -/
noncomputable def cocharacterLatticeFunctorIsoDual :
    cocharacterLatticeFunctor (k := k) ≅
      (characterLatticeFunctor (k := k)).op ⋙ GaloisLatticeCat.dualFunctor :=
  NatIso.ofComponents (fun T ↦ ObjectProperty.isoMk _
    (eqToIso (cocharacterLatticeFunctor_obj_obj T) ≪≫
      cocharacterRepresentationIsoDual T.unop ≪≫
      (eqToIso (congrArg Rep.dual (characterLatticeFunctor_obj_obj T.unop))).symm ≪≫
      (eqToIso (GaloisLatticeCat.dualFunctor_obj_obj _)).symm)) (fun {X Y} f ↦ by
    apply ObjectProperty.hom_ext
    dsimp
    simpa [cocharacterLatticeFunctor_map_hom, GaloisLatticeCat.dualFunctor_map_hom,
      characterLatticeFunctor_map_hom, Category.assoc] using
      congrArg (fun g ↦ eqToHom (cocharacterLatticeFunctor_obj_obj X) ≫ g ≫
        eqToHom (congrArg Rep.dual (characterLatticeFunctor_obj_obj Y.unop)).symm ≫
        eqToHom (GaloisLatticeCat.dualFunctor_obj_obj _).symm)
        (cocharacterRepresentationIsoDual_naturality f.unop))

/-- The comparison with the dual character functor evaluates a cocharacter on a character. -/
@[simp]
theorem cocharacterLatticeFunctorIsoDual_hom_app_apply (T : TorusCommHopfAlgCat k)
    (y : MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
      (toMultiplicativeTypeCommHopfAlgCat T))
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    (eqToHom ((GaloisLatticeCat.dualFunctor_obj_obj _).trans
      (congrArg Rep.dual (characterLatticeFunctor_obj_obj T)))).hom
        (((cocharacterLatticeFunctorIsoDual (k := k)).hom.app (Opposite.op T)).hom
          ((eqToHom (cocharacterLatticeFunctor_obj_obj (Opposite.op T)).symm).hom y)) x =
      MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
        (toMultiplicativeTypeCommHopfAlgCat T) y x := by
  have h : eqToHom (cocharacterLatticeFunctor_obj_obj (Opposite.op T)).symm ≫
      ((cocharacterLatticeFunctorIsoDual (k := k)).hom.app (Opposite.op T)).hom ≫
        eqToHom ((GaloisLatticeCat.dualFunctor_obj_obj _).trans
          (congrArg Rep.dual (characterLatticeFunctor_obj_obj T))) =
      (cocharacterRepresentationIsoDual T).hom := by
    simp [cocharacterLatticeFunctorIsoDual, Category.assoc]
  -- Evaluate the categorical equality after cancelling all object transports.
  exact congrArg (fun g ↦ g.hom y x) h

/-- Over a perfect field, the geometric cocharacter-lattice functor classifies tori.
Its variance is contravariant here because the source consists of coordinate Hopf algebras. -/
noncomputable instance cocharacterLatticeFunctor_isEquivalence [PerfectField k] :
    (cocharacterLatticeFunctor (k := k)).IsEquivalence :=
  Functor.isEquivalence_of_iso (cocharacterLatticeFunctorIsoDual (k := k)).symm

end TauCeti.TorusCommHopfAlgCat
