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
`CategoryTheory.GrothendieckTopology.cohomologyPresheafEvaluationIsoFunctorOverH`: restriction
to the open subspace is transported to the over site, where its cohomology computes the original
cohomology on the open.
-/

public noncomputable section

open CategoryTheory Limits Opposite

namespace TopologicalSpace.Opens

universe u

variable {X : TopCat.{u}}

/-- An isomorphism of sheaves after restriction to `U` induces an isomorphism on cohomology
on `U`, in every degree. -/
def cohomologyIsoOfRestrictIso (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (e : U.sheafRestrict.obj F ≅ U.sheafRestrict.obj G) (n : ℕ) :
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
