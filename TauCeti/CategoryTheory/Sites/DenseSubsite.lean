/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# A sheaf is the right Kan extension of its restriction to a dense subsite

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)`, and let `A` be a category with
the limits indexed by the comma categories `StructuredArrow X G.op`. Mathlib proves that
restriction along `G` is an equivalence `Sheaf K A ≌ Sheaf J A` (the comparison lemma), with
inverse the right Kan extension `G.op.ran`. This file records the consequence for a single sheaf
`ℱ` on `D`: the unit `ℱ ⟶ G.op.ran.obj (G.op ⋙ ℱ)` of the Kan-extension adjunction is an
isomorphism, so `ℱ` itself, with the identity as counit, is the pointwise right Kan extension of
its restriction `G.op ⋙ ℱ` along `G.op`. In other words, for every object `X` of `D` the value
`ℱ.obj (op X)` is the limit of the values `ℱ.obj (op (G.obj Y))` over the arrows
`G.obj Y ⟶ X`, with the restriction maps of `ℱ` as the legs.

For the inclusion of a basis of a topological space into its opens, this says that a sheaf is
determined on every open `V` by its values on the basic opens contained in `V`: it is the
adaptedness of `TopCat.Presheaf.IsAdapted` for every sheaf.

## Main results

* `CategoryTheory.Functor.IsDenseSubsite.isIso_ranAdjunction_unit_app`: the unit of the
  Kan-extension adjunction is an isomorphism at a sheaf.
* `CategoryTheory.Functor.IsDenseSubsite.isRightKanExtension`: a sheaf, with the identity as
  counit, is a right Kan extension of its restriction to a dense subsite.
* `CategoryTheory.Functor.IsDenseSubsite.isPointwiseRightKanExtension`: a sheaf is the pointwise
  right Kan extension of its restriction to a dense subsite.

## References

* P. T. Johnstone, *Sketches of an Elephant*, C2.2, the comparison lemma, which Mathlib
  formalizes as `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`.
-/

public section

universe w w' v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {A : Type w} [Category.{w'} A] [∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]
  [G.IsDenseSubsite J K]

include J in
/-- **The unit of the Kan-extension adjunction is an isomorphism at a sheaf.** For a sheaf `ℱ`
on a site with dense subsite `G`, the canonical map `ℱ ⟶ G.op.ran.obj (G.op ⋙ ℱ)` is an
isomorphism: it is the unit of the sheaf equivalence of the comparison lemma, read in presheaves.
-/
theorem isIso_ranAdjunction_unit_app (ℱ : Sheaf K A) :
    IsIso ((G.op.ranAdjunction A).unit.app ℱ.obj) := by
  rw [← G.sheafAdjunctionCocontinuous_unit_app_hom A J K ℱ]
  -- restriction to a dense subsite is fully faithful on sheaves, so the unit of its adjunction
  -- with `G.op.ran` is an isomorphism; `Sheaf.Hom.hom` is `(sheafToPresheaf K A).map`
  exact inferInstanceAs
    (IsIso ((sheafToPresheaf K A).map ((G.sheafAdjunctionCocontinuous A J K).unit.app ℱ)))

include J in
/-- A sheaf `ℱ`, with the identity as counit, is a right Kan extension of its restriction
`G.op ⋙ ℱ` along `G.op`. -/
theorem isRightKanExtension (ℱ : Sheaf K A) :
    ℱ.obj.IsRightKanExtension (𝟙 (G.op ⋙ ℱ.obj)) :=
  (G.op.isIso_ranAdjunction_unit_app_iff ℱ.obj).mp (isIso_ranAdjunction_unit_app G J K ℱ)

include J in
/-- **A sheaf is the pointwise right Kan extension of its restriction to a dense subsite.** For
every object `X` of `D`, the restriction maps of `ℱ` exhibit `ℱ.obj (op X)` as the limit of the
values `ℱ.obj (op (G.obj Y))` over the arrows `G.obj Y ⟶ X`. -/
noncomputable def isPointwiseRightKanExtension (ℱ : Sheaf K A) :
    (RightExtension.mk ℱ.obj (𝟙 (G.op ⋙ ℱ.obj))).IsPointwiseRightKanExtension :=
  haveI := isRightKanExtension G J K ℱ
  isPointwiseRightKanExtensionOfIsRightKanExtension ℱ.obj (𝟙 (G.op ⋙ ℱ.obj))

end CategoryTheory.Functor.IsDenseSubsite

end
