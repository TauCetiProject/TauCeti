/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.EssentialImage
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Character.SeparableDescent

/-!
# Tori and Galois lattices over arbitrary fields

The geometric character-lattice functor is an equivalence from coordinate Hopf algebras of
tori over any field to continuous integral Galois lattices. On the corresponding group
schemes this is the usual anti-equivalence. Fullness follows by descending equivariant geometric
character maps through the separable closure; faithfulness and essential surjectivity already
hold over arbitrary fields.

The separable closure splits both tori and is Galois over the ground field. No choice of
a finite splitting field is needed to recover a morphism from its character map.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.
-/

public section

open CategoryTheory

namespace TauCeti.TorusCommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- Over any field, every equivariant morphism of character lattices is induced by
a morphism of torus coordinate Hopf algebras. -/
noncomputable instance characterLatticeFunctor_full :
    (characterLatticeFunctor (k := k)).Full where
  map_surjective {S T} f := by
    let q := eqToHom (characterLatticeFunctor_obj_obj S).symm ≫ f.hom ≫
      eqToHom (characterLatticeFunctor_obj_obj T)
    have hS := S.property.multiplicativeType
    obtain ⟨g, hg⟩ :=
      hS.geometricCharacterRepresentationMap_surjective_of_multiplicativeType
        T.property.multiplicativeType q
    refine ⟨ObjectProperty.homMk (ObjectProperty.homMk g), ?_⟩
    apply ObjectProperty.hom_ext
    simp only [characterLatticeFunctor_map_hom, ObjectProperty.homMk_hom, hg, q]
    simp

/-- The character-lattice functor classifies tori over any field. Its variance here
is covariant because the source category consists of coordinate Hopf algebras. -/
noncomputable instance characterLatticeFunctor_isEquivalence :
    (characterLatticeFunctor (k := k)).IsEquivalence where

end TauCeti.TorusCommHopfAlgCat
