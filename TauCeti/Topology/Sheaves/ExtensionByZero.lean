/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Over
public import TauCeti.CategoryTheory.Sites.ExtensionByZero
public import TauCeti.Topology.Sheaves.Skyscraper

/-!
# Extension by zero along an open subset

Let `U` be an open subset of a topological space `X`, and let `A` be a category with a zero object
admitting sheafification on `X`, such as the category of modules over a ring or of abelian groups.
Extension by zero `j_!` sends a sheaf `F` on `U` to the sheaf on `X` whose stalks are those of `F`
at points of `U` and zero elsewhere. It is the left adjoint of restriction to `U`.

Mathlib's `TopologicalSpace.Opens.sheafEquivOver` identifies sheaves on `U` with sheaves on the
slice `Over U` of the site of open subsets of `X`, and `TopologicalSpace.Opens.extendByZero`
is this identification followed by the canonical sheaf pullback along `Over.forget U`. It is
also the sheafification of the presheaf extension by zero
`TauCeti.CategoryTheory.PresheafExtensionByZero.functor`
(`TopologicalSpace.Opens.extendByZeroIsoSheafify`), so
`TauCeti.CategoryTheory.SheafExtensionByZero.preservesFiniteLimits_sheafPullback` shows that
extension by zero preserves finite limits.

## Main declarations

* `TopologicalSpace.Opens.extendByZero`: extension by zero of sheaves from `U` to `X`.
* `TopologicalSpace.Opens.extendByZeroIsoSheafPullback`: extension by zero is the sheaf pullback
  along `Over.forget U` after the identification `TopologicalSpace.Opens.sheafEquivOver`.
* `TopologicalSpace.Opens.extendByZeroAdjunction`: extension by zero is left adjoint to
  `TopologicalSpace.Opens.sheafRestrict`. In particular it preserves all colimits.
* `TopologicalSpace.Opens.extendByZeroIsoSheafify`: extension by zero is the sheafification of the
  presheaf extension by zero.
* `TopologicalSpace.Opens.preservesFiniteLimits_extendByZero`: extension by zero preserves finite
  limits.
* `TopologicalSpace.Opens.extendByZeroCompStalkFunctorIso`: at a point of `U`, the stalk of the
  extension by zero of `F` is naturally the stalk of `F`.
* `TopologicalSpace.Opens.isZero_stalk_extendByZero_obj`: at a point outside `U`, the stalk of the
  extension by zero is zero.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.1.19.
* P. Scholze, *Étale cohomology of diamonds*, proof of Theorem 16.1 and Lemma 20.4.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X)

section

variable (A : Type*) [Category* A] [HasZeroObject A] [HasZeroMorphisms A]
  [HasSheafify (Opens.grothendieckTopology X) A]

/-- Extension by zero of sheaves with values in `A` along the inclusion of an open subset `U`.
It is the identification of sheaves on `U` with sheaves on the slice site `Over U`, followed by the
sheaf pullback along `Over.forget U`. -/
noncomputable def extendByZero :
    Sheaf (Opens.grothendieckTopology U) A ⥤ X.Sheaf A :=
  U.sheafEquivOver.inverse ⋙ (Over.forget U).sheafPullback A
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)

/-- Extension by zero is the identification of sheaves on `U` with sheaves on the slice site
`Over U`, followed by the sheaf pullback along `Over.forget U`. -/
noncomputable def extendByZeroIsoSheafPullback :
    U.extendByZero A ≅ U.sheafEquivOver.inverse ⋙ (Over.forget U).sheafPullback A
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X) :=
  Iso.refl _

/-- Extension by zero is left adjoint to restriction to the open subset `U`. -/
noncomputable def extendByZeroAdjunction : U.extendByZero A ⊣ U.sheafRestrict :=
  (U.sheafEquivOver.symm.toAdjunction.comp
    ((Over.forget U).sheafAdjunctionContinuous A _ _)).ofNatIsoRight
    U.overPullbackSheafEquivOver

/-- Extension by zero is the sheafification of the presheaf extension by zero outside the lower
interval of `U`. -/
noncomputable def extendByZeroIsoSheafify :
    U.extendByZero A ≅ U.sheafEquivOver.inverse ⋙ sheafToPresheaf _ A ⋙
      TauCeti.CategoryTheory.PresheafExtensionByZero.functor U ⋙ presheafToSheaf _ A :=
  U.extendByZeroIsoSheafPullback A ≪≫ U.sheafEquivOver.inverse.isoWhiskerLeft
    (TauCeti.CategoryTheory.SheafExtensionByZero.sheafPullbackIsoSheafify U _)

/-- Extension by zero is a left adjoint, so it preserves all colimits. -/
instance isLeftAdjoint_extendByZero : (U.extendByZero A).IsLeftAdjoint :=
  (U.extendByZeroAdjunction A).isLeftAdjoint

/-- Extension by zero preserves finite limits. -/
instance preservesFiniteLimits_extendByZero [HasFiniteLimits A] :
    PreservesFiniteLimits (U.extendByZero A) :=
  preservesFiniteLimits_of_natIso (U.extendByZeroIsoSheafPullback A).symm

end

section Stalks

variable {A : Type*} [Category.{u} A] [HasZeroObject A] [HasZeroMorphisms A] [HasColimits A]
  [HasSheafify (Opens.grothendieckTopology X) A]

/-- At a point `x` of `U`, the stalk of the extension by zero of a sheaf `F` on `U` is the stalk
of `F` at `x`, naturally in `F`. -/
noncomputable def extendByZeroCompStalkFunctorIso (x : U) :
    U.extendByZero A ⋙ TopCat.Sheaf.forget A X ⋙ TopCat.Presheaf.stalkFunctor A (x : X) ≅
      TopCat.Sheaf.forget A (TopCat.of U) ⋙
        TopCat.Presheaf.stalkFunctor (X := TopCat.of U) A x := by
  classical
  exact ((U.extendByZeroAdjunction A).comp
    (stalkSkyscraperSheafAdjunction (x : X))).leftAdjointUniq
    ((stalkSkyscraperSheafAdjunction (X := TopCat.of U) x).ofNatIsoRight
      (U.skyscraperSheafFunctorCompSheafRestrictIso A x).symm)

/-- At a point outside `U`, the stalk of the extension by zero of any sheaf on `U` is zero. -/
theorem isZero_stalk_extendByZero_obj (F : Sheaf (Opens.grothendieckTopology U) A) {x : X}
    (hx : x ∉ U) : IsZero (((U.extendByZero A).obj F).presheaf.stalk x) := by
  classical
  let adj := (U.extendByZeroAdjunction A).comp (stalkSkyscraperSheafAdjunction x)
  -- Maps from the stalk to `M` correspond to maps from `F` to the restriction of the skyscraper
  -- sheaf at `x`, whose sections over every open subset of `U` form a terminal object.
  have (M : A) : Subsingleton (F ⟶ (skyscraperSheafFunctor x ⋙ U.sheafRestrict).obj M) :=
    ⟨fun f g ↦ by
      ext V
      refine (isTerminalSkyscraperSheafObjObjOfNotMem fun h ↦ hx ?_).hom_ext _ _
      obtain ⟨y, -, rfl⟩ := h
      exact y.property⟩
  exact (IsZero.iff_id_eq_zero _).2 ((adj.homEquiv F _).injective (Subsingleton.elim _ _))

end Stalks

end TopologicalSpace.Opens
