/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Equivalence
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Over
public import TauCeti.CategoryTheory.Sites.ExtensionByZero
public import TauCeti.Topology.Sheaves.Cohomology.Instances
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.Functors

/-!
# Cohomology depends only on the restricted sheaf

The sheaf cohomology `Hⁿ(U, F)` of an abelian sheaf `F` on an open subset `U` of a topological
space `X` is naturally isomorphic to the global cohomology `Hⁿ(U, F|_U)` of its restriction
`U.sheafRestrict.obj F` (`TopologicalSpace.Opens.cohomologyPresheafObjIsoSheafRestrictH`). In
particular, an isomorphism between the restrictions of two abelian sheaves to `U` induces an
isomorphism on their cohomology over `U` (`TopologicalSpace.Opens.cohomologyIsoOfRestrictIso`),
allowing local trivializations and open-subset structure theorems to transport acyclicity without
requiring an isomorphism on the whole space.

The construction uses the localized-site comparison
`CategoryTheory.GrothendieckTopology.cohomologyPresheafEvaluationIsoFunctorOverH` together with site
invariance along `TopologicalSpace.Opens.overEquivalence`.
-/

public noncomputable section

open CategoryTheory Limits Opposite

namespace TopologicalSpace.Opens

universe u

variable {X : TopCat.{u}}

/-- Restricting abelian sheaves to an open subset preserves finite colimits. -/
instance preservesFiniteColimits_sheafRestrict (U : Opens X) :
    PreservesFiniteColimits (U.sheafRestrict (C := AddCommGrpCat.{u})) := by
  have hp : PreservesFiniteColimits
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion') := by
    have := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      U.inclusion').leftAdjoint_preservesColimits.{0, 0}
    infer_instance
  -- Supply preservation explicitly so that instance search need not unfold the
  -- source functor of the naive restriction comparison.
  exact @preservesFiniteColimits_of_natIso _ _ _ _ _ _
    (U.isOpenEmbedding.sheafPullbackIso (A := AddCommGrpCat.{u})) hp

/-- Restricting abelian sheaves to the over site of an open subset preserves finite colimits. -/
instance preservesFiniteColimits_overPullback (U : Opens X) :
    PreservesFiniteColimits ((Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} U) :=
  preservesFiniteColimits_of_natIso
    (U.sheafRestrictSheafEquivOver (A := AddCommGrpCat.{u}))

/-- The cohomology of an abelian sheaf at an open subset `U` is naturally isomorphic to the global
cohomology of its restriction `U.sheafRestrict.obj F` on the open subspace `U`. -/
def cohomologyPresheafEvaluationIsoSheafRestrictFunctorH (U : Opens X) (n : ℕ) :
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      U.sheafRestrict ⋙ Sheaf.functorH (Opens.grothendieckTopology U) n := by
  let J := Opens.grothendieckTopology X
  let JU := Opens.grothendieckTopology U
  let P := J.overPullback AddCommGrpCat.{u} U
  let E := (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor
  let CU := Sheaf.cohomologyPresheafFunctor JU n ⋙
    (evaluation (Opens U)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  exact J.cohomologyPresheafEvaluationIsoFunctorOverH U n ≪≫
    Functor.isoWhiskerLeft P
      ((Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over U) n
        (isTerminalTop.isTerminalObj U.overEquivalence.inverse)).symm ≪≫
      (TauCeti.CategoryTheory.cohomologyPresheafEvaluationIsoSheafCongr (J.over U) JU
        U.overEquivalence n (⊤ : Opens U)).symm) ≪≫
    (Functor.associator P E CU).symm ≪≫
    Functor.isoWhiskerRight (U.overPullbackSheafEquivOver (A := AddCommGrpCat.{u})) CU ≪≫
    Functor.isoWhiskerLeft U.sheafRestrict
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH JU n isTerminalTop)

/-- The cohomology `Hⁿ(U, F)` of an abelian sheaf `F` on an open subset `U` is isomorphic to the
global cohomology `Hⁿ(U, F|_U)` of the restricted sheaf `U.sheafRestrict.obj F`. -/
def cohomologyPresheafObjIsoSheafRestrictH (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H' F n U ≅ AddCommGrpCat.of (Sheaf.H (U.sheafRestrict.obj F) n) :=
  (U.cohomologyPresheafEvaluationIsoSheafRestrictFunctorH n).app F

/-- An isomorphism of sheaves after restriction to `U` induces an isomorphism on cohomology
on `U`, in every degree. -/
def cohomologyIsoOfRestrictIso (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (e : U.sheafRestrict.obj F ≅ U.sheafRestrict.obj G) (n : ℕ) :
    Sheaf.H' F n U ≅ Sheaf.H' G n U := by
  let e' : F.over U ≅ G.over U :=
    (U.sheafRestrictSheafEquivOver.app F).symm ≪≫
      U.sheafEquivOver.inverse.mapIso e ≪≫ U.sheafRestrictSheafEquivOver.app G
  let η := (Opens.grothendieckTopology X).cohomologyPresheafEvaluationIsoFunctorOverH U n
  exact η.app F ≪≫ (Sheaf.functorH _ n).mapIso e' ≪≫ (η.app G).symm

/-- The identity of the restricted sheaf induces the identity on cohomology. -/
@[simp]
theorem cohomologyIsoOfRestrictIso_refl (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    U.cohomologyIsoOfRestrictIso (Iso.refl _) n = Iso.refl (Sheaf.H' F n U) := by
  simp [cohomologyIsoOfRestrictIso]

/-- Composing isomorphisms of restricted sheaves composes the induced cohomology isomorphisms. -/
theorem cohomologyIsoOfRestrictIso_trans (U : Opens X) {F G H : X.Sheaf AddCommGrpCat.{u}}
    (e₁ : U.sheafRestrict.obj F ≅ U.sheafRestrict.obj G)
    (e₂ : U.sheafRestrict.obj G ≅ U.sheafRestrict.obj H) (n : ℕ) :
    U.cohomologyIsoOfRestrictIso (e₁ ≪≫ e₂) n =
      U.cohomologyIsoOfRestrictIso e₁ n ≪≫ U.cohomologyIsoOfRestrictIso e₂ n := by
  simp [cohomologyIsoOfRestrictIso]

end TopologicalSpace.Opens
