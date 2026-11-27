/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.AlgebraicGeometry.Sites.Big.Pushforward
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
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

Both inverse images preserve colimits as left adjoints. The inverse image of `ε` is exact, that
is it also preserves finite limits, when `A` has finite limits and fppf sheafification preserves
them (`HasSheafify`). For `a_X`, `AlgebraicGeometry.Scheme.preservesFiniteLimits_aXPullback` only
reduces exactness to the exactness of the left Kan extension along the inclusion
`X.Etale ⥤ Over X`, which it takes as a hypothesis. That hypothesis carries the content: Mathlib
derives it from representable flatness (`CategoryTheory.lan_preservesFiniteLimits_of_flat`) only
for small categories, and `X.Etale` is not small, so the inclusion being representably flat does
not discharge it here. The unconditional exactness of the inverse image of `a_X` remains open.

The morphism `a_X` factors through `ε`: its direct image is the direct image of `ε` followed by
the restriction of big étale sheaves to the small étale site
(`AlgebraicGeometry.Scheme.aXPushforwardIsoComp`).

The morphism `a_X` is compatible with base change along a morphism `f : Y ⟶ X`: restricting to
étale `X`-schemes after the big direct image along `f` (`T ↦ F(T ×_X Y)`) is the small étale
direct image after restricting to étale `Y`-schemes
(`AlgebraicGeometry.Scheme.aXPushforwardBaseChangeIso`), and dually for the inverse images
(`AlgebraicGeometry.Scheme.aXPullbackBaseChangeIso`). Both direct images are restrictions along
the same functor `X.Etale ⥤ Over Y`, `V ↦ V ×_X Y`. The big inverse image along `f` is the
restriction along `Over.map f`, left adjoint to the big direct image since
`Over.map f ⊣ Over.pullback f`. The morphism `ε` is compatible with base change in the same way:
regarding the big direct image of an fppf sheaf as an étale sheaf is the big étale direct image of
the underlying étale sheaf (`AlgebraicGeometry.Scheme.epsilonFppfEtalePushforwardBaseChangeIso`),
and dually for the inverse images
(`AlgebraicGeometry.Scheme.epsilonFppfEtalePullbackBaseChangeIso`). The big direct and inverse
images along `f` are `AlgebraicGeometry.Scheme.Hom.bigPushforward`, defined for any topology on
schemes in `TauCeti/AlgebraicGeometry/Sites/Big/Pushforward.lean`, and Mathlib's
`CategoryTheory.GrothendieckTopology.overMapPullback`.

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
* `AlgebraicGeometry.Scheme.aXPushforwardBaseChangeIso`,
  `AlgebraicGeometry.Scheme.aXPullbackBaseChangeIso`: compatibility of `a_X` with base change.
* `AlgebraicGeometry.Scheme.epsilonFppfEtalePushforwardBaseChangeIso`,
  `AlgebraicGeometry.Scheme.epsilonFppfEtalePullbackBaseChangeIso`: compatibility of `ε` with base
  change.

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

/- The direct image of `ε` is fully faithful: a morphism of fppf sheaves is the same as a
morphism of the underlying étale sheaves. -/
example : (epsilonFppfEtalePushforward X A).FullyFaithful :=
  fullyFaithfulSheafPushforwardContinuousId (etaleTopology.over X) (fppfTopology.over X) A

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

/- For an fppf sheaf `F`, the fppf sheafification of its underlying étale sheaf is `F` again: the
counit of `epsilonFppfEtaleAdjunction` is an isomorphism, by Mathlib's instance
`CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful`. -/
example : IsIso (epsilonFppfEtaleAdjunction X A).counit :=
  inferInstance

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
  -- `simp` leaves `𝟙 (F.obj.obj (op ((Etale.forget X).obj x.unop))) = 𝟙 (((aXPushforward X A).obj
  -- F).obj.obj x)`. The two objects agree by unfolding `sheafPushforwardContinuous`
  -- (`Functor.sheafPushforwardContinuous_obj_obj_obj`), but `simp` cannot rewrite an object inside
  -- the dependent type of an identity morphism, so `rfl` closes the goal.
  ext; simp [aXPushforwardIsoComp]; rfl

/-- The components of the inverse of `aXPushforwardIsoComp` are identities. -/
@[simp]
theorem aXPushforwardIsoComp_inv_app_hom (F : Sheaf (fppfTopology.over X) A) :
    ((aXPushforwardIsoComp X A).inv.app F).hom = 𝟙 _ := by
  -- As in `aXPushforwardIsoComp_hom_app_hom`, `rfl` closes an equation of two identities.
  ext; simp [aXPushforwardIsoComp]; rfl

section AXPullback

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
Kan extension and both sheafifications preserve finite limits. This reduces exactness to the
exactness of the left Kan extension, which is assumed rather than proved: Mathlib proves it from
representable flatness only for small categories, and `X.Etale` is not small. -/
instance preservesFiniteLimits_aXPullback
    [∀ F : X.Etaleᵒᵖ ⥤ A, (Etale.forget X).op.HasLeftKanExtension F]
    [HasSheafify (smallEtaleTopology X) A] [HasSheafify (fppfTopology.over X) A]
    [PreservesFiniteLimits ((Etale.forget X).op.lan : (X.Etaleᵒᵖ ⥤ A) ⥤ (Over X)ᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (aXPullback X A) := by
  -- Mathlib's construction also asks for the inclusion to be representably flat, which holds as
  -- it preserves finite limits; flatness alone does not give the exactness of the Kan extension.
  have : RepresentablyFlat (Etale.forget X) := flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

end AXPullback

/-! ### Compatibility of `a_X` with base change -/

section BaseChange

variable {X} {Y : Scheme.{u}} (f : Y ⟶ X)

/-- **`a_X` commutes with base change, direct images.** For `f : Y ⟶ X`, restricting the big direct
image of an fppf sheaf on `Y`-schemes to étale `X`-schemes is the small étale direct image of its
restriction to étale `Y`-schemes: both are restriction along `V ↦ V ×_X Y` from `X.Etale` to
`Over Y` (`Hom.smallEtaleBaseChangeCompForgetIso`). -/
noncomputable def aXPushforwardBaseChangeIso :
    f.bigPushforward fppfTopology A ⋙ aXPushforward X A ≅
      aXPushforward Y A ⋙ f.smallEtalePushforward A :=
  letI := Functor.isContinuous_comp f.smallEtaleBaseChange (Etale.forget Y) (smallEtaleTopology X)
    (smallEtaleTopology Y) (fppfTopology.over Y)
  Functor.sheafPushforwardContinuousComp' f.smallEtaleBaseChangeCompForgetIso.symm A
      (smallEtaleTopology X) (fppfTopology.over X) (fppfTopology.over Y) ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

/-- On sections over an étale `X`-scheme `V`, `aXPushforwardBaseChangeIso` is the restriction
along `Hom.smallEtaleBaseChangeCompForgetIso`, whose underlying morphism of schemes is the
identity of `V ×_X Y`. -/
@[simp]
theorem aXPushforwardBaseChangeIso_hom_app_hom_app (F : Sheaf (fppfTopology.over Y) A)
    (V : X.Etaleᵒᵖ) :
    ((aXPushforwardBaseChangeIso A f).hom.app F).hom.app V =
      F.obj.map (f.smallEtaleBaseChangeCompForgetIso.hom.app V.unop).op := by
  -- `simp` reaches `F.obj.map _ ≫ 𝟙 _`, but cannot rewrite the object inside the identity, which
  -- agrees with the expected one only up to unfolding, so `Category.comp_id` closes the goal.
  simp only [Functor.comp_obj, aXPushforwardBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv,
    Functor.sheafPushforwardContinuousComp_inv_app_hom_app]
  exact Category.comp_id _

/-- On sections over an étale `X`-scheme `V`, the inverse of `aXPushforwardBaseChangeIso` is the
restriction along the inverse of `Hom.smallEtaleBaseChangeCompForgetIso`. -/
@[simp]
theorem aXPushforwardBaseChangeIso_inv_app_hom_app (F : Sheaf (fppfTopology.over Y) A)
    (V : X.Etaleᵒᵖ) :
    ((aXPushforwardBaseChangeIso A f).inv.app F).hom.app V =
      F.obj.map (f.smallEtaleBaseChangeCompForgetIso.inv.app V.unop).op := by
  -- As in `aXPushforwardBaseChangeIso_hom_app_hom_app`, with the identity on the left.
  simp only [Functor.comp_obj, aXPushforwardBaseChangeIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.symm_hom]
  exact Category.id_comp _

section Pullback

variable [(aXPushforward X A).IsRightAdjoint] [(aXPushforward Y A).IsRightAdjoint]
  [(f.smallEtalePushforward A).IsRightAdjoint]

/-- **`a_X` commutes with base change, inverse images.** For `f : Y ⟶ X`, pulling an étale sheaf
on `X` back to the small étale site of `Y` and then to the big fppf site of `Y` is the same as
pulling it back to the big fppf site of `X` and then along `f`: the left adjoints of the two
composites in `aXPushforwardBaseChangeIso` agree. -/
noncomputable def aXPullbackBaseChangeIso :
    f.smallEtalePullback A ⋙ aXPullback Y A ≅ aXPullback X A ⋙ fppfTopology.overMapPullback A f :=
  ((f.smallEtaleAdjunction A).comp (aXAdjunction Y A)).leftAdjointUniq
    (((aXAdjunction X A).comp (f.bigAdjunction fppfTopology A)).ofNatIsoRight
      (aXPushforwardBaseChangeIso A f))

/-- `aXPullbackBaseChangeIso` is characterized by the units of the two composite adjunctions: it
carries the unit through the small étale site of `Y` to the unit through the big fppf site of `X`,
followed by `aXPushforwardBaseChangeIso`. -/
@[reassoc]
theorem unit_aXPullbackBaseChangeIso_hom :
    ((f.smallEtaleAdjunction A).comp (aXAdjunction Y A)).unit ≫
        Functor.whiskerRight (aXPullbackBaseChangeIso A f).hom
          (aXPushforward Y A ⋙ f.smallEtalePushforward A) =
      ((aXAdjunction X A).comp (f.bigAdjunction fppfTopology A)).unit ≫
        Functor.whiskerLeft (aXPullback X A ⋙ fppfTopology.overMapPullback A f)
          (aXPushforwardBaseChangeIso A f).hom := by
  rw [aXPullbackBaseChangeIso, Adjunction.unit_leftAdjointUniq_hom]
  simp [Adjunction.ofNatIsoRight]

end Pullback

/-! ### Compatibility of `ε` with base change -/

/-- **`ε` commutes with base change, direct images.** For `f : Y ⟶ X`, regarding the big direct
image of an fppf sheaf on `Y`-schemes as an étale sheaf is the big étale direct image of the
underlying étale sheaf: both are restriction along `Over.pullback f`. -/
noncomputable def epsilonFppfEtalePushforwardBaseChangeIso :
    f.bigPushforward fppfTopology A ⋙ epsilonFppfEtalePushforward X A ≅
      epsilonFppfEtalePushforward Y A ⋙ f.bigPushforward etaleTopology A :=
  -- `Functor.sheafPushforwardContinuous G` sends a sheaf `F` to the sheaf with underlying presheaf
  -- `G.op ⋙ F.obj`. The direct image of `ε` is the case `G = 𝟭 (Over _)`, and composing with
  -- `(𝟭 (Over _)).op` is definitionally the identity, so both composites send `F` to the sheaf
  -- with underlying presheaf `(Over.pullback f).op ⋙ F.obj`, on the same morphisms; they are
  -- equal by unfolding, and `Iso.refl` typechecks.
  Iso.refl _

/-- The components of `epsilonFppfEtalePushforwardBaseChangeIso` are identities. -/
@[simp]
theorem epsilonFppfEtalePushforwardBaseChangeIso_hom_app_hom
    (F : Sheaf (fppfTopology.over Y) A) :
    ((epsilonFppfEtalePushforwardBaseChangeIso A f).hom.app F).hom = 𝟙 _ := by
  -- The iso is `Iso.refl _`, so each component is the identity of `(Over.pullback f).op ⋙ F.obj`;
  -- the two sides differ only in how that presheaf is written (through
  -- `Functor.sheafPushforwardContinuous` and `𝟭 (Over _)`), which `rfl` unfolds.
  ext; rfl

/-- The components of the inverse of `epsilonFppfEtalePushforwardBaseChangeIso` are identities. -/
@[simp]
theorem epsilonFppfEtalePushforwardBaseChangeIso_inv_app_hom
    (F : Sheaf (fppfTopology.over Y) A) :
    ((epsilonFppfEtalePushforwardBaseChangeIso A f).inv.app F).hom = 𝟙 _ := by
  -- As in `epsilonFppfEtalePushforwardBaseChangeIso_hom_app_hom`.
  ext; rfl

section EpsilonPullback

variable [HasWeakSheafify (fppfTopology.over X) A] [HasWeakSheafify (fppfTopology.over Y) A]

/-- **`ε` commutes with base change, inverse images.** For `f : Y ⟶ X`, restricting a big étale
sheaf on `X`-schemes along `f` and then sheafifying for the fppf topology of `Y` is the same as
sheafifying for the fppf topology of `X` and then restricting along `f`: the left adjoints of the
two composites in `epsilonFppfEtalePushforwardBaseChangeIso` agree. -/
noncomputable def epsilonFppfEtalePullbackBaseChangeIso :
    etaleTopology.overMapPullback A f ⋙ epsilonFppfEtalePullback Y A ≅
      epsilonFppfEtalePullback X A ⋙ fppfTopology.overMapPullback A f :=
  ((f.bigAdjunction etaleTopology A).comp (epsilonFppfEtaleAdjunction Y A)).leftAdjointUniq
    (((epsilonFppfEtaleAdjunction X A).comp (f.bigAdjunction fppfTopology A)).ofNatIsoRight
      (epsilonFppfEtalePushforwardBaseChangeIso A f))

/-- `epsilonFppfEtalePullbackBaseChangeIso` is characterized by the units of the two composite
adjunctions: it carries the unit through the big étale site of `Y` to the unit through the big
fppf site of `X`, followed by `epsilonFppfEtalePushforwardBaseChangeIso`. -/
@[reassoc]
theorem unit_epsilonFppfEtalePullbackBaseChangeIso_hom :
    ((f.bigAdjunction etaleTopology A).comp (epsilonFppfEtaleAdjunction Y A)).unit ≫
        Functor.whiskerRight (epsilonFppfEtalePullbackBaseChangeIso A f).hom
          (epsilonFppfEtalePushforward Y A ⋙ f.bigPushforward etaleTopology A) =
      ((epsilonFppfEtaleAdjunction X A).comp (f.bigAdjunction fppfTopology A)).unit ≫
        Functor.whiskerLeft (epsilonFppfEtalePullback X A ⋙ fppfTopology.overMapPullback A f)
          (epsilonFppfEtalePushforwardBaseChangeIso A f).hom := by
  rw [epsilonFppfEtalePullbackBaseChangeIso, Adjunction.unit_leftAdjointUniq_hom]
  simp [Adjunction.ofNatIsoRight]

end EpsilonPullback

end BaseChange

end AlgebraicGeometry.Scheme
