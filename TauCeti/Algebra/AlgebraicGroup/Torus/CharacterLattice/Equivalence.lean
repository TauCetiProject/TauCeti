/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.EssentialImage
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Character.Descent

/-!
# Tori and Galois lattices over perfect fields

The geometric character-lattice functor is an equivalence from coordinate Hopf algebras of
tori over a perfect field to continuous integral Galois lattices. On the corresponding group
schemes this is the usual anti-equivalence. Fullness follows by descending equivariant geometric
character maps; faithfulness and essential surjectivity hold over arbitrary fields.

The perfectness assumption is used only for descent from the algebraic closure. No choice of
splitting field is needed to recover a morphism from its character map.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.
-/

public section

open CategoryTheory

namespace TauCeti.TorusCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [PerfectField k]

/-- Over a perfect field, every equivariant morphism of character lattices is induced by
a morphism of torus coordinate Hopf algebras. -/
noncomputable instance characterLatticeFunctor_full :
    (characterLatticeFunctor (k := k)).Full where
  map_surjective {S T} f := by
    let q := eqToHom (characterLatticeFunctor_obj_obj S).symm ≫ f.hom ≫
      eqToHom (characterLatticeFunctor_obj_obj T)
    obtain ⟨g, hg⟩ := S.property.multiplicativeType.geometricCharacterRepresentationMap_surjective q
    refine ⟨ObjectProperty.homMk (ObjectProperty.homMk g), ?_⟩
    apply ObjectProperty.hom_ext
    simp only [characterLatticeFunctor_map_hom, ObjectProperty.homMk_hom, hg, q]
    simp

/-- The character-lattice functor classifies tori over a perfect field. Its variance here
is covariant because the source category consists of coordinate Hopf algebras. -/
noncomputable instance characterLatticeFunctor_isEquivalence :
    (characterLatticeFunctor (k := k)).IsEquivalence where

end TauCeti.TorusCommHopfAlgCat
