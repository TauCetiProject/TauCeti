/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent

/-!
# Functoriality of dual cotangent maps on finite-type commutative Hopf algebras

This file provides `FiniteTypeCommHopfAlgCat` functoriality lemmas for `Derivation.dualCotangentMap`
composed with `FiniteTypeCommHopfAlgCat.toBialgHom`.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.dualCotangentMap_toBialgHom_id` and
  `TauCeti.FiniteTypeCommHopfAlgCat.dualCotangentMap_toBialgHom_comp`: functoriality of
  `Derivation.dualCotangentMap ∘ toBialgHom` in `FiniteTypeCommHopfAlgCat`.
-/

public section

namespace TauCeti.FiniteTypeCommHopfAlgCat

open CategoryTheory Derivation

section Functoriality

universe u v

variable {R : Type u} [CommRing R]

/-- The dual cotangent map of the identity morphism in `FiniteTypeCommHopfAlgCat` acts as the
identity. -/
theorem dualCotangentMap_toBialgHom_id (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    dualCotangentMap (toBialgHom (𝟙 H)) x = x := by
  rw [toBialgHom_id, dualCotangentMap_id, LinearMap.id_apply]

/-- The dual cotangent map of a composite morphism in `FiniteTypeCommHopfAlgCat` is the
contravariant composite of the dual cotangent maps. -/
theorem dualCotangentMap_toBialgHom_comp {H K L : FiniteTypeCommHopfAlgCat.{u, v} R}
    (f : H ⟶ K) (g : K ⟶ L) (x : Module.Dual R (Bialgebra.CotangentSpace R L)) :
    dualCotangentMap (toBialgHom f) (dualCotangentMap (toBialgHom g) x) =
      dualCotangentMap (toBialgHom (f ≫ g)) x := by
  rw [toBialgHom_comp, dualCotangentMap_comp, LinearMap.comp_apply]

end Functoriality

end TauCeti.FiniteTypeCommHopfAlgCat
