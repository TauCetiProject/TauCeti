/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Functoriality
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Faithful

/-!
# Faithfulness of the torus character-lattice functor

Morphisms of tori over any field are determined by their pullbacks on geometric character
lattices. This is the uniqueness part of the classification of tori by Galois lattices.
The result follows from character detection for groups of multiplicative type and does not
require choosing a finite splitting field.
-/

public section

open CategoryTheory

namespace TauCeti.TorusCommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- The geometric character-lattice functor is faithful over every field. -/
instance characterLatticeFunctor_faithful :
    (characterLatticeFunctor (k := k)).Faithful where
  map_injective {S T} f g hfg := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply S.property.multiplicativeType.geometricCharacterRepresentationMap_injective
    have h := congrArg (fun q ↦ q.hom) hfg
    simpa only [characterLatticeFunctor_map_hom, cancel_epi, cancel_mono] using h

end TauCeti.TorusCommHopfAlgCat
