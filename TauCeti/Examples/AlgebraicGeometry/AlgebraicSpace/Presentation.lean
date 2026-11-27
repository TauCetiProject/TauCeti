/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Presentation

/-!
# The presentation of a scheme by its identity atlas

For a scheme `X`, the identity of its functor of points is an étale atlas. The scheme
`R = X ×_X X` representing its kernel pair has equal projections to `X`, and they are
isomorphisms: the presentation of `X` given by `spacePresentation` is `(X, Δ)`, and the quotient
sheaf of this relation is the functor of points of `X`.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry Spaces

universe u

namespace TauCeti.SpacePresentationExample

variable (X : Scheme.{u})

/-- The identity atlas of a scheme. -/
theorem etaleAtlas_id : EtaleAtlas (𝟙 (yoneda.obj X)) := .of_isIso _

/-- The two projections of the relation of the identity atlas agree. -/
theorem fst'_eq_snd :
    (etaleAtlas_id X).relativelyRepresentable.fst' (𝟙 (yoneda.obj X)) =
      (etaleAtlas_id X).relativelyRepresentable.snd (𝟙 (yoneda.obj X)) :=
  Functor.relativelyRepresentable.fst'_self_eq_snd_of_mono _

/-- The projections of the relation of the identity atlas are isomorphisms, so the relation is
the diagonal of `X`. -/
theorem isIso_snd :
    IsIso ((etaleAtlas_id X).relativelyRepresentable.snd (𝟙 (yoneda.obj X))) :=
  Functor.relativelyRepresentable.isIso_snd_self_of_mono _

/-- The quotient sheaf of the relation of the identity atlas is the functor of points of `X`. -/
noncomputable def quotientSheafIso :
    quotientSheaf ((etaleAtlas_id X).relativelyRepresentable.snd (𝟙 (yoneda.obj X)))
        ((etaleAtlas_id X).relativelyRepresentable.fst' (𝟙 (yoneda.obj X))) ≅
      uliftSheaf (IsAlgebraicSpace.yoneda_obj X).isSheaf :=
  spacePresentation _ (etaleAtlas_id X)

end TauCeti.SpacePresentationExample
