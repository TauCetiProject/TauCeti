/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.AlgebraicGeometry.Sites.Etale.Subcanonical
public import TauCeti.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.CategoryTheory.Sites.ComparableTopologies

/-!
# The comparison morphisms from fppf sheaves to étale sheaves

Let `X` be a scheme. Every étale covering family is an fppf covering family, since étale
morphisms are flat and locally of finite presentation, so the big étale topology is coarser than
the big fppf topology (`AlgebraicGeometry.Scheme.etaleTopology_le_fppfTopology`), and the same
holds for the induced topologies on the category `Over X` of `X`-schemes. This gives two
morphisms of topoi, each described through its direct image and its inverse image, a left adjoint
of the direct image.

* `ε : (Sch/X)_fppf → (Sch/X)_ét`, induced by the identity of `Over X`. Its direct image
  `AlgebraicGeometry.Scheme.epsilonFppfEtalePushforward X A` regards an fppf sheaf as an étale
  sheaf and is fully faithful; its inverse image
  `AlgebraicGeometry.Scheme.epsilonFppfEtalePullback X A` is fppf sheafification, left adjoint to
  the direct image (`AlgebraicGeometry.Scheme.epsilonFppfEtaleAdjunction`).
* `a_X : (Sch/X)_fppf → X_ét`, induced by the inclusion `X.Etale ⥤ Over X` of étale `X`-schemes
  among all `X`-schemes, which is continuous from the small étale topology to the big fppf
  topology. Its direct image `AlgebraicGeometry.Scheme.aXPushforward X A` restricts a big fppf
  sheaf to the étale `X`-schemes; its inverse image `AlgebraicGeometry.Scheme.aXPullback X A` is
  Mathlib's `CategoryTheory.Functor.sheafPullback`, left adjoint to it
  (`AlgebraicGeometry.Scheme.aXAdjunction`), which exists for instance when the left Kan
  extensions along the inclusion exist and fppf sheafification does.

Both inverse images preserve colimits as left adjoints. They are exact, that is they also
preserve finite limits, under the corresponding hypotheses on `A`: for `ε` when `A` has finite
limits and fppf sheafification preserves them (`HasSheafify`), and for `a_X` when moreover the
left Kan extension along the inclusion `X.Etale ⥤ Over X` preserves finite limits
(`AlgebraicGeometry.Scheme.preservesFiniteLimits_aXPullback`), the inclusion being representably
flat as it preserves finite limits.

The morphism `a_X` factors through `ε`: its direct image is the direct image of `ε` followed by
the restriction of big étale sheaves to the small étale site
(`AlgebraicGeometry.Scheme.aXPushforwardIsoComp`).

The site `Over X` is large (its objects form a type in the universe above that of the morphisms),
so the existence of fppf sheafification on it (`HasWeakSheafify`) and of the inverse image of
`a_X` are hypotheses of the inverse images rather than constructions.

## Main declarations

* `AlgebraicGeometry.Scheme.epsilonFppfEtalePushforward`,
  `AlgebraicGeometry.Scheme.epsilonFppfEtalePullback`,
  `AlgebraicGeometry.Scheme.epsilonFppfEtaleAdjunction`: the morphism `ε`.
* `AlgebraicGeometry.Scheme.aXPushforward`, `AlgebraicGeometry.Scheme.aXPullback`,
  `AlgebraicGeometry.Scheme.aXAdjunction`: the morphism `a_X`.
* `AlgebraicGeometry.Scheme.aXPushforwardIsoComp`: the direct image of `a_X` is that of `ε`
  followed by restriction to the small étale site.

## References

* [Stacks Project, Section 59.100](https://stacks.math.columbia.edu/tag/0DDK), *Comparing
  fppf and étale topologies*.
-/

public section

universe v' u u'

open CategoryTheory Limits TauCeti.CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (A : Type u') [Category.{v'} A]

/-! ### The morphism `ε` from big fppf sheaves to big étale sheaves -/

/-- The direct image of the morphism of topoi `ε : (Sch/X)_fppf → (Sch/X)_ét`: an fppf sheaf on
`X`-schemes is an étale sheaf. -/
abbrev epsilonFppfEtalePushforward :
    Sheaf (fppfTopology.over X) A ⥤ Sheaf (etaleTopology.over X) A :=
  (𝟭 (Over X)).sheafPushforwardContinuous A (etaleTopology.over X) (fppfTopology.over X)

/-- The direct image of `ε` is fully faithful: a morphism of fppf sheaves is the same as a
morphism of the underlying étale sheaves. -/
def fullyFaithfulEpsilonFppfEtalePushforward :
    (epsilonFppfEtalePushforward X A).FullyFaithful :=
  fullyFaithfulSheafPushforwardContinuousId _ _ A

section Pullback

variable [HasWeakSheafify (fppfTopology.over X) A]

/-- The inverse image of the morphism of topoi `ε : (Sch/X)_fppf → (Sch/X)_ét`: the fppf
sheafification of an étale sheaf on `X`-schemes. -/
noncomputable abbrev epsilonFppfEtalePullback :
    Sheaf (etaleTopology.over X) A ⥤ Sheaf (fppfTopology.over X) A :=
  sheafToPresheaf (etaleTopology.over X) A ⋙ presheafToSheaf (fppfTopology.over X) A

/-- The inverse image of `ε`, fppf sheafification, is left adjoint to its direct image, the
inclusion of fppf sheaves into étale sheaves. -/
noncomputable abbrev epsilonFppfEtaleAdjunction :
    epsilonFppfEtalePullback X A ⊣ epsilonFppfEtalePushforward X A :=
  sheafifyAdjunctionPushforwardId (etaleTopology.over X) (fppfTopology.over X) A

/-- For an fppf sheaf `F`, the fppf sheafification of its underlying étale sheaf is `F` again: the
counit of `epsilonFppfEtaleAdjunction` is an isomorphism. -/
instance isIso_epsilonFppfEtaleAdjunction_counit :
    IsIso (epsilonFppfEtaleAdjunction X A).counit :=
  (epsilonFppfEtaleAdjunction X A).counit_isIso_of_R_fully_faithful

/- The inverse image of `ε` is exact when `A` has finite limits and fppf sheafification preserves
them. -/
example [HasFiniteLimits A] [HasSheafify (fppfTopology.over X) A] :
    PreservesFiniteLimits (epsilonFppfEtalePullback X A) :=
  inferInstance

end Pullback

/-! ### The morphism `a_X` from big fppf sheaves to small étale sheaves -/

/-- The inclusion of étale `X`-schemes among all `X`-schemes is continuous from the small étale
topology to the big fppf topology, so restricting an fppf sheaf gives a sheaf on the small étale
site. -/
instance : (Etale.forget X).IsContinuous (smallEtaleTopology X) (fppfTopology.over X) :=
  Functor.isContinuous_comp' (F₁ := Etale.forget X) (F₂ := 𝟭 (Over X)) (Functor.rightUnitor _)
    (smallEtaleTopology X) (etaleTopology.over X) (fppfTopology.over X)

/-- The direct image of the morphism of topoi `a_X : (Sch/X)_fppf → X_ét`: the restriction of a
big fppf sheaf on `X`-schemes to the étale `X`-schemes. -/
abbrev aXPushforward : Sheaf (fppfTopology.over X) A ⥤ Sheaf (smallEtaleTopology X) A :=
  (Etale.forget X).sheafPushforwardContinuous A (smallEtaleTopology X) (fppfTopology.over X)

/-- The direct image of `a_X` is the direct image of `ε` followed by the restriction of big étale
sheaves on `X`-schemes to the small étale site. -/
noncomputable def aXPushforwardIsoComp :
    aXPushforward X A ≅ epsilonFppfEtalePushforward X A ⋙
      (Etale.forget X).sheafPushforwardContinuous A (smallEtaleTopology X)
        (etaleTopology.over X) :=
  (Functor.sheafPushforwardContinuousComp' (F := Etale.forget X) (G := 𝟭 (Over X))
    (Functor.rightUnitor (Etale.forget X)) A
    (smallEtaleTopology X) (etaleTopology.over X) (fppfTopology.over X)).symm

/-- The components of `aXPushforwardIsoComp` are identities. -/
@[simp]
theorem aXPushforwardIsoComp_hom_app_hom (F : Sheaf (fppfTopology.over X) A) :
    ((aXPushforwardIsoComp X A).hom.app F).hom = 𝟙 _ := by
  ext; simp [aXPushforwardIsoComp]; rfl

/-- The components of the inverse of `aXPushforwardIsoComp` are identities. -/
@[simp]
theorem aXPushforwardIsoComp_inv_app_hom (F : Sheaf (fppfTopology.over X) A) :
    ((aXPushforwardIsoComp X A).inv.app F).hom = 𝟙 _ := by
  ext; simp [aXPushforwardIsoComp]; rfl

/- The inverse image of `a_X` exists when the left Kan extensions along the inclusion of étale
`X`-schemes among all `X`-schemes and fppf sheafification exist, by Mathlib's construction
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`. -/
example [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasLeftKanExtension F]
    [HasWeakSheafify (fppfTopology.over X) A] : (aXPushforward X A).IsRightAdjoint :=
  inferInstance

variable [(aXPushforward X A).IsRightAdjoint]

/-- The inverse image of the morphism of topoi `a_X : (Sch/X)_fppf → X_ét`, Mathlib's pullback of
sheaves along the inclusion of étale `X`-schemes among all `X`-schemes. -/
noncomputable abbrev aXPullback : Sheaf (smallEtaleTopology X) A ⥤ Sheaf (fppfTopology.over X) A :=
  (Etale.forget X).sheafPullback A (smallEtaleTopology X) (fppfTopology.over X)

/-- The inverse image of `a_X` is left adjoint to its direct image. -/
noncomputable abbrev aXAdjunction : aXPullback X A ⊣ aXPushforward X A :=
  (Etale.forget X).sheafAdjunctionContinuous A (smallEtaleTopology X) (fppfTopology.over X)

/-- The inverse image of `a_X` is exact when it is computed by left Kan extension along the
inclusion of étale `X`-schemes among all `X`-schemes followed by fppf sheafification, and the left
Kan extension and both sheafifications preserve finite limits. -/
instance preservesFiniteLimits_aXPullback
    [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasLeftKanExtension F]
    [HasSheafify (smallEtaleTopology X) A] [HasSheafify (fppfTopology.over X) A]
    [PreservesFiniteLimits ((Etale.forget X).op.lan : (X.Etaleᵒᵖ ⥤ A) ⥤ (Over X)ᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (aXPullback X A) := by
  -- The inclusion is representably flat, as it preserves finite limits.
  have : RepresentablyFlat (Etale.forget X) := flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

end AlgebraicGeometry.Scheme
