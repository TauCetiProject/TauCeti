/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import TauCeti.AlgebraicTopology.SimplicialNerve.Quasicategory

/-!
# The simplicial category of Kan complexes and the quasicategory `Spaces`

The full simplicial subcategory `SSet.SpacesΔ` of `SSet` spanned by the Kan complexes has mapping
simplicial sets `Fun(A, B)`, which are themselves Kan complexes (`SSet.SpacesΔ.kanComplex_sHom`).
Its simplicial (homotopy coherent) nerve is `SSet.spaces`, the quasicategory of small spaces
(HTT Definition 1.2.16.1), which is a quasicategory by
`CategoryTheory.SimplicialNerve.quasicategory` (`SSet.spaces.quasicategory`).

## Main definitions

* `SSet.SpacesΔ`: the full simplicial subcategory of `SSet` spanned by the Kan complexes.
* `SSet.spaces`: the simplicial nerve of `SSet.SpacesΔ`, the quasicategory of small spaces.

## Main results

* `SSet.SpacesΔ.kanComplex_sHom`: the mapping simplicial sets of `SSet.SpacesΔ` are Kan complexes.
* `SSet.spaces.quasicategory`: `SSet.spaces` is a quasicategory.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.1.5.10 and Definition 1.2.16.1.
-/

public section

open CategoryTheory MonoidalClosed SimplicialCategory

universe u

namespace SSet

/-- The simplicial category of small Kan complexes, realized as the full simplicial subcategory of
`SSet` spanned by the Kan complexes. Its mapping simplicial sets are the function complexes
`Fun(A, B)`. -/
abbrev SpacesΔ : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun A : SSet.{u} ↦ KanComplex A

/-- The simplicial (homotopy coherent) nerve of `SpacesΔ`, the quasicategory of small spaces whose
vertices are the Kan complexes in universe `u`. -/
noncomputable abbrev spaces : SSet.{u + 1} :=
  SimplicialNerve SpacesΔ.{u}

namespace SpacesΔ

/-- The mapping simplicial sets of `SpacesΔ` are Kan complexes, as function complexes into Kan
complexes. -/
instance kanComplex_sHom (A B : SpacesΔ.{u}) : KanComplex (sHom A B) :=
  have := B.property
  inferInstanceAs (KanComplex ((ihom A.obj).obj B.obj))

end SpacesΔ

/-- **HTT Proposition 1.1.5.10**: the simplicial nerve `Spaces` of small Kan complexes is a
quasicategory, as `SpacesΔ` is locally Kan. -/
instance spaces.quasicategory : Quasicategory spaces.{u} :=
  CategoryTheory.SimplicialNerve.quasicategory SpacesΔ.{u}

end SSet
