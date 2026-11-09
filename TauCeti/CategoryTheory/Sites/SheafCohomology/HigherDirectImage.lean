/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.CategoryTheory.Sites.Continuous
public import TauCeti.CategoryTheory.Sites.Homology
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution

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
resolution `I` of `F`, the sheaf `Rⁱf_* F` is the `i`-th homology of `f_* I`. More generally, for
every resolution `L` of `F` whose terms have no higher cohomology over any object of `D`, the
`i`-th homology of `f_* L` is the sheafification of the objectwise homology `V ↦ Hⁱ(L(u(V)))`
(`CategoryTheory.GrothendieckTopology.homologyFunctorIsoSheafify`), and the sections of `L` over
`u(V)` compute `Hⁱ(u(V), F)` (`CategoryTheory.Sheaf.H'.homologyIsoCohomologyPresheaf`). This is
`CategoryTheory.Functor.sheafPushforwardContinuousHomologyIsoSheafify`; the generality matters for
sheaves of modules, whose injective resolutions are flasque but not injective as abelian
sheaves.

## Main declarations

* `CategoryTheory.Functor.sheafHigherDirectImage`: the higher direct images `Rⁱf_*` of a morphism of
  sites.
* `CategoryTheory.Functor.sheafHigherDirectImageZeroIso`: `R⁰f_* ≅ f_*`.
* `CategoryTheory.Functor.sheafPushforwardContinuousHomologyIsoSheafify`: for an acyclic
  resolution `L` of `F`, the homology of `f_* L` is the sheafification of `V ↦ Hⁱ(u(V), F)`.
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
  [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]

section Resolution

variable {F : Sheaf K AddCommGrpCat.{v}} {L : CochainComplex (Sheaf K AddCommGrpCat.{v}) ℕ}
  (ι : F ⟶ L.X 0) [Mono ι] (hι : ι ≫ L.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (L.d 0 1) hι).Exact) (hL : ∀ j, L.ExactAt (j + 1))
  (hLV : ∀ V j k, Subsingleton ((L.X j).H' (k + 1) V)) (i : ℕ)

/-- **Pushforwards of acyclic resolutions compute sheafified cohomology presheaves.** For a
resolution `0 ⟶ F ⟶ L⁰ ⟶ L¹ ⟶ ⋯` of an abelian sheaf `F` on `(D, K)` whose terms have no
cohomology in positive degrees over any object of `D`, the `i`-th homology of the pushforward
complex `f_* L` along `u : C ⥤ D` is the sheafification of the presheaf `V ↦ Hⁱ(u(V), F)` on
`C`. -/
noncomputable def sheafPushforwardContinuousHomologyIsoSheafify :
    (((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).mapHomologicalComplex _).obj
      L).homology i ≅
      (presheafToSheaf J AddCommGrpCat.{v}).obj (u.op ⋙ F.cohomologyPresheaf i) :=
  let W := (whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{v}).obj u.op
  (J.homologyFunctorIsoSheafify AddCommGrpCat.{v} _ i).app _ ≪≫
    (presheafToSheaf J AddCommGrpCat.{v}).mapIso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso
        -- the presheaf underlying the pushforward of a sheaf is its composite with `u.op`
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).app L ≪≫
          (NatIso.mapHomologicalComplex
            (u.sheafPushforwardContinuousCompSheafToPresheafIso AddCommGrpCat.{v} J K) _).app
              L ≪≫
          ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).app L).symm) ≪≫
        (W.mapHomologicalComplexCompHomologyFunctorIso _ i).app _ ≪≫
        W.mapIso (Sheaf.H'.homologyIsoCohomologyPresheaf ι hι hι' hL hLV i))

end Resolution

variable [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{v})]

/-- **Higher direct images are sheafified cohomology presheaves.** For an abelian sheaf `F` on
`(D, K)`, the higher direct image `Rⁱf_* F` along `u : C ⥤ D` is the sheafification of the presheaf
`V ↦ Hⁱ(u(V), F)` on `C`. -/
noncomputable def sheafHigherDirectImageObjIsoSheafify (F : Sheaf K AddCommGrpCat.{v}) (i : ℕ) :
    (u.sheafHigherDirectImage AddCommGrpCat.{v} J K i).obj F ≅
      (presheafToSheaf J AddCommGrpCat.{v}).obj (u.op ⋙ F.cohomologyPresheaf i) :=
  let R := injectiveResolution F
  R.isoRightDerivedObj _ i ≪≫
    u.sheafPushforwardContinuousHomologyIsoSheafify J K (R.ι.f 0) R.ι_f_zero_comp_complex_d
      R.exact₀ R.cocomplex_exactAt_succ
      (fun _ _ _ ↦ Abelian.Ext.subsingleton_of_injective _ _ _) i

end CategoryTheory.Functor
