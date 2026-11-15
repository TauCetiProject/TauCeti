/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.SimplicialSet.SmallModel

/-!
# Locally small simplicial sets

A quasicategory living in a large universe, such as the nerve of a category of `u`-small sets,
is *locally `u`-small* when each of its mapping spaces has the homotopy type of a `u`-small Kan
complex. The simplices of a mapping space need not form a `u`-small type for this: local
smallness concerns homotopy types, not sets of simplices. This is the universe control needed
to send the coherent representable functors `Map_C(x, -)` to the quasicategory of `u`-small
spaces, and to define compact objects and presentable quasicategories.

Here `SSet.IsLocallySmall.{u} X` asks every right mapping space `Hom^R_X(x, y)` to admit a
small Kan model in universe `u` (`TauCeti.HasSmallSpaceModel`), and `SSet.smallMappingSpace X x y`
is a chosen such model, a Kan complex in universe `u`, with comparison maps inverse up to
simplicial homotopy (`SSet.smallMappingSpaceModel X x y`).

For a strict Segal simplicial set, such as the nerve of a category, the right mapping spaces
are discrete on the edges (`SSet.rightMappingSpace.constEdgeIso`), and a discrete simplicial set
has a small model exactly when its set of vertices is small. Hence a strict Segal simplicial set
is locally `u`-small exactly when its sets of edges between two vertices are `u`-small
(`SSet.isLocallySmall_iff_of_isStrictSegal`). For nerves this recovers Mathlib's notion:
the nerve of a category is locally `u`-small exactly when the category is
(`CategoryTheory.nerve.isLocallySmall_iff`). In particular the nerve of the category of `u`-small
types is locally `u`-small, whereas the nerve of a category whose morphisms between two objects
do not form a `u`-small type is not.

## Main definitions

* `SSet.IsLocallySmall.{u} X`: every right mapping space of `X` has a Kan model in universe `u`.
* `SSet.smallMappingSpaceModel X x y`: a chosen small model of `Hom^R_X(x, y)` with its
  comparison maps and homotopies, and `SSet.smallMappingSpace X x y`, its underlying Kan complex.

## Main results

* `SSet.isLocallySmall_iff_of_isStrictSegal`: a strict Segal simplicial set is locally `u`-small
  exactly when its sets of edges are `u`-small.
* `CategoryTheory.nerve.isLocallySmall_iff`: the nerve of a category is locally `u`-small exactly
  when the category is locally `u`-small.

## References

* J. Lurie, *Higher Topos Theory*, Corollary 5.4.1.5 and Proposition 5.4.1.7.
-/

public section

open CategoryTheory Simplicial

universe u v w

namespace SSet

/-- A simplicial set `X` is *locally `u`-small* when each right mapping space `Hom^R_X(x, y)` has
the homotopy type of a Kan complex in universe `u`. Only the homotopy types of the mapping
spaces are constrained, not the sizes of their sets of simplices. The notion is intended for
quasicategories, whose right mapping spaces model their spaces of maps. -/
class IsLocallySmall (X : SSet.{v}) : Prop where
  /-- Every right mapping space has a small Kan model. -/
  hasSmallSpaceModel (x y : X _⦋0⦌) :
    TauCeti.HasSmallSpaceModel.{u} (X.rightMappingSpace x y : SSet.{v})

variable (X : SSet.{v})

/-- A chosen small Kan model of the right mapping space `Hom^R_X(x, y)` of a locally `u`-small
simplicial set, with comparison maps inverse to each other up to simplicial homotopy after
lifting both to a common universe. -/
noncomputable def smallMappingSpaceModel [IsLocallySmall.{u} X] (x y : X _⦋0⦌) :
    TauCeti.SmallSpaceModel.{u} (X.rightMappingSpace x y : SSet.{v}) :=
  ((TauCeti.hasSmallSpaceModel_iff_nonempty _).1 (IsLocallySmall.hasSmallSpaceModel x y)).some

/-- The small mapping space of a locally `u`-small simplicial set: the Kan complex in universe
`u` underlying the chosen small model of `Hom^R_X(x, y)`. -/
noncomputable abbrev smallMappingSpace [IsLocallySmall.{u} X] (x y : X _⦋0⦌) : SSet.{u} :=
  (X.smallMappingSpaceModel x y).model

/-- A strict Segal simplicial set, such as the nerve of a category, is locally `u`-small exactly
when the edges between any two of its vertices form a `u`-small type: its right mapping spaces
are the discrete simplicial sets on these edges. -/
theorem isLocallySmall_iff_of_isStrictSegal [X.IsStrictSegal] :
    IsLocallySmall.{u} X ↔ ∀ x y : X _⦋0⦌, Small.{u} (X.Edge x y) := by
  simp_rw [← TauCeti.hasSmallSpaceModel_const_iff,
    TauCeti.hasSmallSpaceModel_iff_of_iso (rightMappingSpace.constEdgeIso _ _)]
  exact ⟨fun h ↦ h.hasSmallSpaceModel, fun h ↦ ⟨h⟩⟩

end SSet

namespace CategoryTheory.nerve

variable {C : Type w} [Category.{v} C]

/-- The nerve of a category is locally `u`-small exactly when the category is locally `u`-small:
its right mapping spaces are the discrete simplicial sets on the morphisms of the category. -/
theorem isLocallySmall_iff : SSet.IsLocallySmall.{u} (nerve C) ↔ LocallySmall.{u} C := by
  rw [SSet.isLocallySmall_iff_of_isStrictSegal]
  refine ⟨fun h ↦ ⟨fun a b ↦ ?_⟩, fun _ x y ↦ (small_congr homEquiv).2 inferInstance⟩
  simpa using (small_congr homEquiv).1 (h (nerveEquiv.symm a) (nerveEquiv.symm b))

/-- The nerve of a locally `u`-small category is locally `u`-small. -/
instance [LocallySmall.{u} C] : SSet.IsLocallySmall.{u} (nerve C) :=
  isLocallySmall_iff.2 inferInstance

end CategoryTheory.nerve
