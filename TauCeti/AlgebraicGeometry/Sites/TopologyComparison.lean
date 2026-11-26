/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Fppf.EtaleComparison
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.EtaleComparison
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.ZariskiComparison

/-!
# Composing the comparison morphisms between the topologies of a scheme

Let `X` be a scheme. The comparison morphisms of topoi
`(Sch/X)_fppf → X_ét → X_Nis → X_Zar` are each induced by a continuous functor of sites: the
inclusion `Etale.forget X : X.Etale ⥤ Over X` of étale `X`-schemes (for `a_X`), the identity of
`X.Etale` (for `X_ét → X_Nis`), and `opensToEtale X : X.Opens ⥤ X.Etale` (for `X_Nis → X_Zar`).
This file composes them.

The functor `opensToEtale X` is continuous from the Zariski topology to the small étale topology,
as the composite of `opensToEtale X` (Zariski to Nisnevich) and the identity (Nisnevich to étale).
This gives the comparison morphism `X_ét → X_Zar`, whose direct image
`AlgebraicGeometry.Scheme.etaleToZariskiPushforward X A` restricts an étale sheaf to the open
subschemes of `X`. Its direct image is the composite of the direct images through `X_Nis`
(`AlgebraicGeometry.Scheme.etaleToZariskiPushforwardIsoComp`), so its inverse image, when the
étale and Nisnevich sheafifications exist, is the composite of the two inverse images
(`AlgebraicGeometry.Scheme.etaleToZariskiAdjunction`,
`AlgebraicGeometry.Scheme.etaleToZariskiPullbackIso`).

Likewise the restriction of a big fppf sheaf to the open subschemes of `X`
(`AlgebraicGeometry.Scheme.fppfToZariskiPushforward X A`, the direct image along
`opensToEtale X ⋙ Etale.forget X`) is the direct image of `a_X` followed by the direct images
through `X_Nis` (`AlgebraicGeometry.Scheme.fppfToZariskiPushforwardIsoComp`), and by
`AlgebraicGeometry.Scheme.aXPushforwardIsoComp` also the direct image of
`ε : (Sch/X)_fppf → (Sch/X)_ét` followed by restriction to the small étale site and then to the
open subschemes. When the inverse image of `a_X` exists, the inverse image of
`(Sch/X)_fppf → X_Zar` is therefore that of `X_ét → X_Zar` followed by that of `a_X`
(`AlgebraicGeometry.Scheme.fppfToZariskiAdjunction`,
`AlgebraicGeometry.Scheme.fppfToZariskiPullbackIso`).

All these isomorphisms are identities: each direct image is restriction along a functor, and the
functors compose on the nose.

## Main declarations

* `AlgebraicGeometry.Scheme.etaleToZariskiPushforward`,
  `AlgebraicGeometry.Scheme.etaleToZariskiPullback`,
  `AlgebraicGeometry.Scheme.etaleToZariskiAdjunction`: the comparison morphism `X_ét → X_Zar`.
* `AlgebraicGeometry.Scheme.etaleToZariskiPushforwardIsoComp`: it factors through `X_Nis`.
* `AlgebraicGeometry.Scheme.etaleToZariskiPullbackIso`: its inverse image is Mathlib's pullback of
  sheaves along `opensToEtale X`.
* `AlgebraicGeometry.Scheme.fppfToZariskiPushforward`,
  `AlgebraicGeometry.Scheme.fppfToZariskiPushforwardIsoComp`: the comparison
  `(Sch/X)_fppf → X_Zar` factors through `a_X`, `X_ét` and `X_Nis`.
* `AlgebraicGeometry.Scheme.fppfToZariskiPullback`,
  `AlgebraicGeometry.Scheme.fppfToZariskiAdjunction`,
  `AlgebraicGeometry.Scheme.fppfToZariskiPullbackIso`: its inverse image, when that of `a_X`
  exists, is the inverse image of `X_ét → X_Zar` followed by that of `a_X`, and is Mathlib's
  pullback of sheaves along `opensToEtale X ⋙ Etale.forget X`.

## References

* [Stacks Project, Section 59.100](https://stacks.math.columbia.edu/tag/0DDK), *Comparing
  fppf and étale topologies*.
-/

public section

universe v' u u'

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (A : Type u') [Category.{v'} A]

/-- The functor `opensToEtale X` is continuous from the Zariski topology to the small étale
topology: it is the composite of `opensToEtale X`, continuous to the small Nisnevich topology,
with the identity of `X.Etale`, continuous from the Nisnevich to the étale topology. -/
instance isContinuous_opensToEtale_smallEtaleTopology :
    (opensToEtale X).IsContinuous (Opens.grothendieckTopology X) (smallEtaleTopology X) :=
  Functor.isContinuous_comp' (F₁ := opensToEtale X) (F₂ := 𝟭 X.Etale)
    (Functor.rightUnitor _) (Opens.grothendieckTopology X) (smallNisnevichTopology X)
    (smallEtaleTopology X)

/-! ### The comparison morphism `X_ét → X_Zar` -/

/-- The direct image of the comparison morphism of topoi `X_ét → X_Zar`: the restriction of an
étale sheaf on `X` to the open subschemes of `X`. -/
noncomputable abbrev etaleToZariskiPushforward :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (Opens.grothendieckTopology X) A :=
  (opensToEtale X).sheafPushforwardContinuous A (Opens.grothendieckTopology X)
    (smallEtaleTopology X)

/-- **The comparisons compose, direct images.** The direct image of `X_ét → X_Zar` is the direct
image of `X_ét → X_Nis` followed by that of `X_Nis → X_Zar`. -/
noncomputable def etaleToZariskiPushforwardIsoComp :
    etaleToZariskiPushforward X A ≅
      etaleToNisnevichPushforward X A ⋙ nisnevichToZariskiPushforward X A :=
  -- Both sides send `F` to the sheaf with underlying presheaf `(opensToEtale X).op ⋙ F.obj`:
  -- composing with `(𝟭 X.Etale).op` is definitionally the identity, so `Iso.refl` typechecks.
  Iso.refl _

/-- The components of `etaleToZariskiPushforwardIsoComp` are identities. -/
@[simp]
theorem etaleToZariskiPushforwardIsoComp_hom_app_hom (F : Sheaf (smallEtaleTopology X) A) :
    ((etaleToZariskiPushforwardIsoComp X A).hom.app F).hom = 𝟙 _ := by
  -- The iso is `Iso.refl _`; the two sides differ only in how the presheaf is written.
  ext; rfl

/-- The components of the inverse of `etaleToZariskiPushforwardIsoComp` are identities. -/
@[simp]
theorem etaleToZariskiPushforwardIsoComp_inv_app_hom (F : Sheaf (smallEtaleTopology X) A) :
    ((etaleToZariskiPushforwardIsoComp X A).inv.app F).hom = 𝟙 _ := by
  -- As in `etaleToZariskiPushforwardIsoComp_hom_app_hom`.
  ext; rfl

section Pullback

variable [HasWeakSheafify (smallEtaleTopology X) A] [HasWeakSheafify (smallNisnevichTopology X) A]

/-- The inverse image of the comparison morphism of topoi `X_ét → X_Zar`: the inverse image of
`X_Nis → X_Zar` followed by that of `X_ét → X_Nis`, that is, the étale sheafification of the
Nisnevich sheafification of the presheaf `V ↦ F(image of V)`. -/
noncomputable abbrev etaleToZariskiPullback :
    Sheaf (Opens.grothendieckTopology X) A ⥤ Sheaf (smallEtaleTopology X) A :=
  nisnevichToZariskiPullback X A ⋙ etaleToNisnevichPullback X A

/-- **The comparisons compose, inverse images.** The inverse image of `X_ét → X_Zar` is left
adjoint to its direct image. -/
noncomputable def etaleToZariskiAdjunction :
    etaleToZariskiPullback X A ⊣ etaleToZariskiPushforward X A :=
  ((nisnevichToZariskiAdjunction X A).comp (etaleToNisnevichAdjunction X A)).ofNatIsoRight
    (etaleToZariskiPushforwardIsoComp X A).symm

noncomputable instance isRightAdjoint_etaleToZariskiPushforward :
    (etaleToZariskiPushforward X A).IsRightAdjoint :=
  (etaleToZariskiAdjunction X A).isRightAdjoint

/-- The inverse image `etaleToZariskiPullback X A` is the general pullback of sheaves along the
continuous functor `opensToEtale X`. -/
noncomputable def etaleToZariskiPullbackIso :
    (opensToEtale X).sheafPullback A (Opens.grothendieckTopology X) (smallEtaleTopology X) ≅
      etaleToZariskiPullback X A :=
  ((opensToEtale X).sheafAdjunctionContinuous A _ _).leftAdjointUniq
    (etaleToZariskiAdjunction X A)

/- The inverse image of `X_ét → X_Zar` is exact when `A` has finite limits and both
sheafifications preserve them. -/
example [HasFiniteLimits A] [HasSheafify (smallEtaleTopology X) A]
    [HasSheafify (smallNisnevichTopology X) A] :
    PreservesFiniteLimits (etaleToZariskiPullback X A) :=
  inferInstance

end Pullback

/-! ### The comparison `(Sch/X)_fppf → X_Zar` -/

/-- The functor `opensToEtale X ⋙ Etale.forget X`, viewing an open subscheme of `X` as an
`X`-scheme, is continuous from the Zariski topology to the big fppf topology. -/
instance isContinuous_opensToEtale_comp_forget :
    (opensToEtale X ⋙ Etale.forget X).IsContinuous (Opens.grothendieckTopology X)
      (fppfTopology.over X) :=
  Functor.isContinuous_comp _ _ _ (smallEtaleTopology X) _

/-- The direct image of the comparison morphism of topoi `(Sch/X)_fppf → X_Zar`: the restriction
of a big fppf sheaf on `X`-schemes to the open subschemes of `X`. -/
noncomputable abbrev fppfToZariskiPushforward :
    Sheaf (fppfTopology.over X) A ⥤ Sheaf (Opens.grothendieckTopology X) A :=
  (opensToEtale X ⋙ Etale.forget X).sheafPushforwardContinuous A (Opens.grothendieckTopology X)
    (fppfTopology.over X)

/-- **The comparisons compose, from the big fppf site.** Restricting a big fppf sheaf to the open
subschemes of `X` is the direct image of `a_X`, followed by those of `X_ét → X_Nis` and
`X_Nis → X_Zar`. -/
noncomputable def fppfToZariskiPushforwardIsoComp :
    fppfToZariskiPushforward X A ≅
      aXPushforward X A ⋙ etaleToNisnevichPushforward X A ⋙ nisnevichToZariskiPushforward X A :=
  -- Both sides send `F` to the sheaf with underlying presheaf
  -- `(opensToEtale X ⋙ Etale.forget X).op ⋙ F.obj`, up to the associativity of composition of
  -- functors and composition with `(𝟭 X.Etale).op`, which hold definitionally.
  Iso.refl _

/-- The components of `fppfToZariskiPushforwardIsoComp` are identities. -/
@[simp]
theorem fppfToZariskiPushforwardIsoComp_hom_app_hom (F : Sheaf (fppfTopology.over X) A) :
    ((fppfToZariskiPushforwardIsoComp X A).hom.app F).hom = 𝟙 _ := by
  -- As in `etaleToZariskiPushforwardIsoComp_hom_app_hom`.
  ext; rfl

/-- The components of the inverse of `fppfToZariskiPushforwardIsoComp` are identities. -/
@[simp]
theorem fppfToZariskiPushforwardIsoComp_inv_app_hom (F : Sheaf (fppfTopology.over X) A) :
    ((fppfToZariskiPushforwardIsoComp X A).inv.app F).hom = 𝟙 _ := by
  -- As in `etaleToZariskiPushforwardIsoComp_hom_app_hom`.
  ext; rfl

section FppfPullback

variable [HasWeakSheafify (smallEtaleTopology X) A] [HasWeakSheafify (smallNisnevichTopology X) A]
  [(aXPushforward X A).IsRightAdjoint]

/-- The inverse image of the comparison morphism of topoi `(Sch/X)_fppf → X_Zar`: the inverse
image of `X_ét → X_Zar` followed by that of `a_X`. -/
noncomputable abbrev fppfToZariskiPullback :
    Sheaf (Opens.grothendieckTopology X) A ⥤ Sheaf (fppfTopology.over X) A :=
  etaleToZariskiPullback X A ⋙ aXPullback X A

/-- The inverse image of `(Sch/X)_fppf → X_Zar` is left adjoint to its direct image. -/
noncomputable def fppfToZariskiAdjunction :
    fppfToZariskiPullback X A ⊣ fppfToZariskiPushforward X A :=
  ((etaleToZariskiAdjunction X A).comp (aXAdjunction X A)).ofNatIsoRight
    (Functor.isoWhiskerLeft _ (etaleToZariskiPushforwardIsoComp X A) ≪≫
      (fppfToZariskiPushforwardIsoComp X A).symm)

noncomputable instance isRightAdjoint_fppfToZariskiPushforward :
    (fppfToZariskiPushforward X A).IsRightAdjoint :=
  (fppfToZariskiAdjunction X A).isRightAdjoint

/-- The inverse image `fppfToZariskiPullback X A` is the general pullback of sheaves along the
continuous functor `opensToEtale X ⋙ Etale.forget X`. -/
noncomputable def fppfToZariskiPullbackIso :
    (opensToEtale X ⋙ Etale.forget X).sheafPullback A (Opens.grothendieckTopology X)
        (fppfTopology.over X) ≅
      fppfToZariskiPullback X A :=
  ((opensToEtale X ⋙ Etale.forget X).sheafAdjunctionContinuous A _ _).leftAdjointUniq
    (fppfToZariskiAdjunction X A)

end FppfPullback

end AlgebraicGeometry.Scheme
