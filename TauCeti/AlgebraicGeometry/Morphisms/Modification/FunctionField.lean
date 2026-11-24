/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

/-!
# Modifications induce isomorphisms of function fields

A modification `f : X ⟶ Y` of irreducible schemes induces an isomorphism
`f^* : K(Y) ⟶ K(X)` of generic stalks (`AlgebraicGeometry.Scheme.Hom.functionFieldMap`); these are
the function fields when `X` and `Y` are integral. The ring isomorphism `K(Y) ≃+* K(X)` is then
`AlgebraicGeometry.Scheme.Hom.functionFieldEquiv f`.

## Main results

* `TauCeti.AlgebraicGeometry.IsModification.isIso_functionFieldMap`: a modification of irreducible
  schemes induces an isomorphism of generic stalks.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.IsModification

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsModification f] [IrreducibleSpace X]
  [IrreducibleSpace Y]

/-- For a modification `f : X ⟶ Y` of irreducible schemes, the pullback
`f.functionFieldMap : K(Y) ⟶ K(X)` of generic stalks (function fields when `X` and `Y` are
integral) is an isomorphism. -/
instance isIso_functionFieldMap : IsIso f.functionFieldMap := by
  -- `f` is an isomorphism over a dense, hence nonempty, open of `Y`
  obtain ⟨U, hU, -, _⟩ := exists_isIso_morphismRestrict (f := f)
  have : Nonempty U := hU.nonempty.to_subtype
  exact f.isIso_functionFieldMap_of_isOpenImmersion_morphismRestrict U

end TauCeti.AlgebraicGeometry.IsModification
