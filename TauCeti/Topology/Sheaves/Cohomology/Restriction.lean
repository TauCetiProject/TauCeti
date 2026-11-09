/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Over
public import TauCeti.CategoryTheory.Sites.ExtensionByZero
public import TauCeti.Topology.Sheaves.Cohomology.Instances
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.Functors

/-!
# Cohomology depends only on the restricted sheaf

An isomorphism between the restrictions of two abelian sheaves to an open subset induces an
isomorphism on their cohomology over that open. This allows local trivializations of sheaves
to transport acyclicity, without requiring an isomorphism on the whole space.

The construction uses the localized-site comparison
`CategoryTheory.Sheaf.cohomologyPresheafObjIsoOverH`: restriction to the open subspace is
transported to the over site, where its cohomology computes the original cohomology on the open.
-/

public noncomputable section

open CategoryTheory Limits Opposite

namespace TopologicalSpace.Opens

universe u

variable {X : TopCat.{u}}

/-- An isomorphism of sheaves after restriction to `U` induces an isomorphism on cohomology
on `U`, in every degree. -/
def cohomologyIsoOfRestrictIso (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (e : (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F ≅
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj G) (n : ℕ) :
    Sheaf.H' F n U ≅ Sheaf.H' G n U := by
  have : PreservesFiniteColimits (U.sheafRestrict (C := AddCommGrpCat.{u})) := by
    have hp : PreservesFiniteColimits
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion') := by
      have := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        U.inclusion').leftAdjoint_preservesColimits.{0, 0}
      infer_instance
    -- Supply preservation explicitly so that instance search need not unfold the
    -- source functor of the naive restriction comparison.
    exact @preservesFiniteColimits_of_natIso _ _ _ _ _ _
      (U.isOpenEmbedding.sheafPullbackIso (A := AddCommGrpCat.{u})) hp
  have : PreservesFiniteColimits
      ((Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} U) :=
    preservesFiniteColimits_of_natIso
      (U.sheafRestrictSheafEquivOver (A := AddCommGrpCat.{u}))
  let e' : F.over U ≅ G.over U :=
    (U.sheafRestrictSheafEquivOver.app F).symm ≪≫
      U.sheafEquivOver.inverse.mapIso e ≪≫ U.sheafRestrictSheafEquivOver.app G
  exact Sheaf.cohomologyPresheafObjIsoOverH F n U ≪≫
    (Sheaf.functorH _ n).mapIso e' ≪≫ (Sheaf.cohomologyPresheafObjIsoOverH G n U).symm

end TopologicalSpace.Opens
