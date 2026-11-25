/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.AlgebraicGeometry.Sites.Etale.Subcanonical
public import TauCeti.CategoryTheory.Sites.ComparableTopologies

/-!
# The comparison morphisms from fppf sheaves to étale sheaves

Let `X` be a scheme. Every étale covering family is an fppf covering family, since étale
morphisms are flat and locally of finite presentation, so the big étale topology is coarser than
the big fppf topology (`AlgebraicGeometry.Scheme.etaleTopology_le_fppfTopology`), and the same
holds for the induced topologies on the category `Over X` of `X`-schemes. This gives two
morphisms of topoi, each described through its direct image and its inverse image.

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

The morphism `a_X` factors through `ε`: its direct image is the direct image of `ε` followed by
the restriction of big étale sheaves to the small étale site
(`AlgebraicGeometry.Scheme.aXPushforwardIsoComp`).

The site `Over X` is large (its objects form a type in the universe above that of the morphisms),
so the existence of fppf sheafification on it (`HasWeakSheafify`) and of the inverse image of
`a_X` are hypotheses of the inverse images rather than constructions.

## Main declarations

* `AlgebraicGeometry.Scheme.etaleTopology_le_fppfTopology`: étale coverings are fppf coverings.
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

/-- **Étale coverings are fppf coverings**: the big étale topology is coarser than the big fppf
topology, as étale morphisms are flat and locally of finite presentation. -/
theorem etaleTopology_le_fppfTopology : etaleTopology.{u} ≤ fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono (precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩)

/-- On `X`-schemes, the big étale topology is coarser than the big fppf topology. -/
theorem etaleTopology_over_le_fppfTopology_over (X : Scheme.{u}) :
    etaleTopology.over X ≤ fppfTopology.over X := fun Y S hS ↦ by
  rw [GrothendieckTopology.mem_over_iff] at hS ⊢
  exact etaleTopology_le_fppfTopology _ hS

variable (X : Scheme.{u}) (A : Type u') [Category.{v'} A]

instance : (𝟭 (Over X)).IsContinuous (etaleTopology.over X) (fppfTopology.over X) :=
  isContinuous_id_of_le (etaleTopology_over_le_fppfTopology_over X)

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

/-- The inverse image of `ε` followed by its direct image gives back an fppf sheaf: the counit of
the adjunction is an isomorphism. -/
instance isIso_epsilonFppfEtaleAdjunction_counit :
    IsIso (epsilonFppfEtaleAdjunction X A).counit :=
  (epsilonFppfEtaleAdjunction X A).counit_isIso_of_R_fully_faithful

end Pullback

/-! ### The morphism `a_X` from big fppf sheaves to small étale sheaves -/

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
  Functor.sheafPushforwardContinuousComp' (Functor.rightUnitor (Etale.forget X)) A
    (smallEtaleTopology X) (etaleTopology.over X) (fppfTopology.over X)

/-- On a big fppf sheaf `F`, the direct image of `a_X` evaluated at an étale `X`-scheme `U` is
`F(U)`. -/
@[simp]
theorem aXPushforward_obj_obj_obj (F : Sheaf (fppfTopology.over X) A) (U : X.Etaleᵒᵖ) :
    ((aXPushforward X A).obj F).obj.obj U = F.obj.obj (Opposite.op ((Etale.forget X).obj U.unop)) :=
  rfl

variable [(aXPushforward X A).IsRightAdjoint]

/-- The inverse image of the morphism of topoi `a_X : (Sch/X)_fppf → X_ét`, Mathlib's pullback of
sheaves along the inclusion of étale `X`-schemes among all `X`-schemes. -/
noncomputable abbrev aXPullback : Sheaf (smallEtaleTopology X) A ⥤ Sheaf (fppfTopology.over X) A :=
  (Etale.forget X).sheafPullback A (smallEtaleTopology X) (fppfTopology.over X)

/-- The inverse image of `a_X` is left adjoint to its direct image. -/
noncomputable abbrev aXAdjunction : aXPullback X A ⊣ aXPushforward X A :=
  (Etale.forget X).sheafAdjunctionContinuous A (smallEtaleTopology X) (fppfTopology.over X)

end AlgebraicGeometry.Scheme
