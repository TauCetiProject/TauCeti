/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.CategoryTheory.Sites.Continuous
public import TauCeti.CategoryTheory.Sites.Homology
public import TauCeti.CategoryTheory.Sites.SheafCohomology.InjectiveResolution

/-!
# Higher direct images along a morphism of sites

Let `u : C ⥤ D` be a continuous functor from a site `(C, J)` to a site `(D, K)`, and let `A` be an
abelian category such that the abelian category of `A`-valued sheaves on `(D, K)` has injective
resolutions (for instance `A = AddCommGrpCat` on a small site, which is then Grothendieck
abelian). The pushforward `f_* = u.sheafPushforwardContinuous A J K`, sending a sheaf `F` on `D`
to `F ∘ u` on `C`, is left exact, and its right derived functors are the higher direct images
`Rⁱf_* = u.sheafHigherDirectImage A J K i`. In degree zero they recover the pushforward
(`CategoryTheory.Functor.sheafHigherDirectImageZeroIso`).

For abelian groups, the higher direct images are sheafified cohomology presheaves: `Rⁱf_* F` is
the sheafification of the presheaf `V ↦ Hⁱ(u(V), F)` on `C`
(`CategoryTheory.Functor.sheafHigherDirectImageObjIsoSheafify`). Indeed, for an injective
resolution `I` of `F`, the sheaf `Rⁱf_* F` is the `i`-th homology of `f_* I`, which is the
sheafification of the objectwise homology `V ↦ Hⁱ(I(u(V)))`
(`CategoryTheory.GrothendieckTopology.homologyFunctorIsoSheafify`), and the sections of `I` over
`u(V)` compute `Hⁱ(u(V), F)`
(`CategoryTheory.InjectiveResolution.homologyIsoCohomologyPresheaf`).

## Main declarations

* `CategoryTheory.Functor.sheafHigherDirectImage`: the higher direct images `Rⁱf_*` of a morphism of
  sites.
* `CategoryTheory.Functor.sheafHigherDirectImageZeroIso`: `R⁰f_* ≅ f_*`.
* `CategoryTheory.Functor.sheafHigherDirectImageObjIsoSheafify`: `Rⁱf_* F` is the sheafification of
  `V ↦ Hⁱ(u(V), F)`.

## References

* [Stacks Project, Lemma 21.7.4 (Tag 072W)](https://stacks.math.columbia.edu/tag/072W).
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.1.
-/

public section

open CategoryTheory Limits Opposite

universe v u₁ v₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v} D] (u : C ⥤ D)

section General

variable (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  [HasInjectiveResolutions (Sheaf K A)]

/-- The higher direct images `Rⁱf_*` along a continuous functor `u : C ⥤ D` between sites: the
right derived functors of the pushforward `F ↦ F ∘ u` from sheaves on `D` to sheaves on `C`. -/
noncomputable abbrev sheafHigherDirectImage (i : ℕ) : Sheaf K A ⥤ Sheaf J A :=
  (u.sheafPushforwardContinuous A J K).rightDerived i

/-- The zeroth higher direct image is the pushforward: `R⁰f_* ≅ f_*`. -/
noncomputable def sheafHigherDirectImageZeroIso :
    u.sheafHigherDirectImage A J K 0 ≅ u.sheafPushforwardContinuous A J K :=
  (u.sheafPushforwardContinuous A J K).rightDerivedZeroIsoSelf

end General

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]

/-- **Higher direct images are sheafified cohomology presheaves.** For an abelian sheaf `F` on
`(D, K)`, the higher direct image `Rⁱf_* F` along `u : C ⥤ D` is the sheafification of the presheaf
`V ↦ Hⁱ(u(V), F)` on `C`. -/
noncomputable def sheafHigherDirectImageObjIsoSheafify (F : Sheaf K AddCommGrpCat.{v}) (i : ℕ) :
    (u.sheafHigherDirectImage AddCommGrpCat.{v} J K i).obj F ≅
      (presheafToSheaf J AddCommGrpCat.{v}).obj (u.op ⋙ F.cohomologyPresheaf i) :=
  let R := injectiveResolution F
  let W := (whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{v}).obj u.op
  R.isoRightDerivedObj _ i ≪≫
    (J.homologyFunctorIsoSheafify AddCommGrpCat.{v} _ i).app _ ≪≫
    (presheafToSheaf J AddCommGrpCat.{v}).mapIso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso
        -- the presheaf underlying the pushforward of a sheaf is its composite with `u.op`
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).app R.cocomplex ≪≫
          (NatIso.mapHomologicalComplex
            (u.sheafPushforwardContinuousCompSheafToPresheafIso AddCommGrpCat.{v} J K) _).app
              R.cocomplex ≪≫
          ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).app R.cocomplex).symm) ≪≫
        (W.mapHomologicalComplexCompHomologyFunctorIso _ i).app _ ≪≫
        W.mapIso (R.homologyIsoCohomologyPresheaf i))

end CategoryTheory.Functor
