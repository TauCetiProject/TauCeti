/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.InjectiveResolution
public import TauCeti.AlgebraicGeometry.Modules.Pushforward.HomologicalComplex
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Flasque

/-!
# Cohomology of an acyclic direct image

For a morphism of schemes `f : X ⟶ Y` and a module sheaf `M` with vanishing positive
higher direct images, `Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)` in every degree, naturally in `M`.
The comparison also holds on every open of `Y`, and respects restriction.

The direct image of a module-injective resolution is a resolution of `f_* M`: vanishing
higher direct images gives exactness in positive degrees, and left exactness gives exactness
at degree zero. Its terms are flasque, so its complex of sections computes cohomology.
This is the acyclic case of the Leray comparison.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Exercise 8.1.
* The Stacks Project, Cohomology on Sites, Section 21.14 (tag 072X).
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Functor
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : X.Modules}

private lemma exactAt_pushforward (P : InjectiveResolution M)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (q : ℕ) :
    (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj P.cocomplex).ExactAt
      (q + 1) := by
  let := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (P.isoRightDerivedObj (Scheme.Modules.pushforward f) (q + 1)).isZero_iff.mp (hM q)

private def pushforwardResolutionCohomologyIso (P : InjectiveResolution M)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((Scheme.Modules.pushforward f ⋙ toSheaf Y).mapHomologicalComplex _).obj
        P.cocomplex)).homology n ≅
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
        ((Scheme.Modules.pushforward f).obj M)).cohomologyPresheaf n := by
  let G := Scheme.Modules.pushforward f ⋙ toSheaf Y
  haveI : Mono (G.map (P.ι.f 0)) := Functor.map_mono _ _
  exact Sheaf.H'.homologyIsoCohomologyPresheaf
    (K := (G.mapHomologicalComplex _).obj P.cocomplex)
    (G.map (P.ι.f 0)) (CochainComplex.map_augmentation_comp_d G P.ι_f_zero_comp_complex_d)
    (P.exact₀.map_of_mono_of_preservesKernel G inferInstance inferInstance)
    (fun q ↦ (exactAt_pushforward f P hM q).map (toSheaf Y))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      ((Scheme.Modules.pushforward f).obj (P.cocomplex.X j)) k V) n

private lemma pushforwardResolutionCohomologyIso_naturality {N : X.Modules}
    (P : InjectiveResolution M) (Q : InjectiveResolution N) (φ : M ⟶ N)
    (ψ : P.cocomplex ⟶ Q.cocomplex) (hψ : P.ι.f 0 ≫ ψ.f 0 = φ ≫ Q.ι.f 0)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M))
    (hN : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj N)) (n : ℕ) :
    HomologicalComplex.homologyMap
      (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (((Scheme.Modules.pushforward f ⋙ toSheaf Y).mapHomologicalComplex _).map ψ)) n ≫
      (pushforwardResolutionCohomologyIso f Q hN n).hom =
    (pushforwardResolutionCohomologyIso f P hM n).hom ≫
      (Sheaf.cohomologyPresheafFunctor _ n).map
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map ((Scheme.Modules.pushforward f).map φ)) := by
  let G := Scheme.Modules.pushforward f ⋙ toSheaf Y
  have : Mono (G.map (P.ι.f 0)) := Functor.map_mono _ _
  have : Mono (G.map (Q.ι.f 0)) := Functor.map_mono _ _
  dsimp only [pushforwardResolutionCohomologyIso]
  exact Sheaf.H'.homologyMap_comp_homologyIsoCohomologyPresheaf_hom
    (K := (G.mapHomologicalComplex _).obj P.cocomplex)
    (K' := (G.mapHomologicalComplex _).obj Q.cocomplex)
    (G.map (P.ι.f 0)) (CochainComplex.map_augmentation_comp_d G P.ι_f_zero_comp_complex_d)
    (P.exact₀.map_of_mono_of_preservesKernel G inferInstance inferInstance)
    (fun q ↦ (exactAt_pushforward f P hM q).map (toSheaf Y))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      ((Scheme.Modules.pushforward f).obj (P.cocomplex.X j)) k V) n
    (G.map (Q.ι.f 0)) (CochainComplex.map_augmentation_comp_d G Q.ι_f_zero_comp_complex_d)
    (Q.exact₀.map_of_mono_of_preservesKernel G inferInstance inferInstance)
    (fun q ↦ (exactAt_pushforward f Q hN q).map (toSheaf Y))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      ((Scheme.Modules.pushforward f).obj (Q.cocomplex.X j)) k V)
    (φ := G.map φ) (ψ := (G.mapHomologicalComplex _).map ψ)
    ((G.map_comp _ _).symm.trans ((congrArg G.map hψ).trans (G.map_comp _ _)))

/-- If all positive higher direct images of `M` vanish, cohomology of its direct image
agrees, over every open, with cohomology of `M` on the inverse image. -/
def cohomologyPresheafPushforwardIsoOfIsZeroHigherDirectImage (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
      ((Scheme.Modules.pushforward f).obj M)).cohomologyPresheaf n ≅
    (Opens.map f.base).op ⋙
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheaf n := by
  let P := injectiveResolution M
  let W := (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (Opens.map f.base).op
  exact (pushforwardResolutionCohomologyIso f P hM n).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((f.pushforwardSectionsComplexIso).app P.cocomplex) ≪≫
    (W.mapHomologicalComplexCompHomologyFunctorIso _ n).app
      (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)) ≪≫
    W.mapIso (P.cohomologyPresheafIso n)

/-- The acyclic direct-image comparison of cohomology presheaves is natural in coefficients. -/
@[reassoc]
lemma cohomologyPresheafPushforwardIsoOfIsZeroHigherDirectImage_naturality
    {M N : X.Modules} (φ : M ⟶ N)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M))
    (hN : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj N)) (n : ℕ) :
    (Sheaf.cohomologyPresheafFunctor _ n).map
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map ((Scheme.Modules.pushforward f).map φ)) ≫
      (cohomologyPresheafPushforwardIsoOfIsZeroHigherDirectImage f N hN n).hom =
    (cohomologyPresheafPushforwardIsoOfIsZeroHigherDirectImage f M hM n).hom ≫
      whiskerLeft (Opens.map f.base).op
        ((Sheaf.cohomologyPresheafFunctor _ n).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)) := by
  let P := injectiveResolution M
  let Q := injectiveResolution N
  let ψ := InjectiveResolution.desc φ Q P
  let W := (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (Opens.map f.base).op
  have h₁ := pushforwardResolutionCohomologyIso_naturality f P Q φ ψ
    (InjectiveResolution.desc_commutes_zero φ Q P) hM hN n
  have h₁' :
      (Sheaf.cohomologyPresheafFunctor _ n).map
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map ((Scheme.Modules.pushforward f).map φ)) ≫
        (pushforwardResolutionCohomologyIso f Q hN n).inv =
      (pushforwardResolutionCohomologyIso f P hM n).inv ≫
        HomologicalComplex.homologyMap
          (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
            (((Scheme.Modules.pushforward f ⋙ toSheaf Y).mapHomologicalComplex _).map ψ)) n := by
    apply (Iso.eq_inv_comp _).2
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h₁.symm =≫
      (pushforwardResolutionCohomologyIso f Q hN n).inv
  have h₂ := congrArg (HomologicalComplex.homologyFunctor _ _ n).map
    ((f.pushforwardSectionsComplexIso).hom.naturality ψ)
  have h₃ := (W.mapHomologicalComplexCompHomologyFunctorIso _ n).hom.naturality
    (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
      (((toSheaf X).mapHomologicalComplex _).map ψ))
  have h₄ := congrArg W.map (InjectiveResolution.cohomologyPresheafIso_naturality P Q φ ψ
    (InjectiveResolution.desc_commutes_zero φ Q P) n)
  simp only [Functor.map_comp, Functor.comp_map] at h₁' h₂ h₃ h₄
  exact ((CommSq.mk h₁').vert_comp ((CommSq.mk h₂).vert_comp
    ((CommSq.mk h₃).vert_comp (CommSq.mk h₄)))).w

/-- **Cohomology of an acyclic direct image.** If `R^{q+1} f_* M = 0` for every `q`,
then `Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)` for every `n`. -/
def cohomologyPushforwardIsoOfIsZeroHigherDirectImage (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    AddCommGrpCat.of (Cohomology ((Scheme.Modules.pushforward f).obj M) n) ≅
      AddCommGrpCat.of (Cohomology M n) :=
  (cohomologyOnTopIso ((Scheme.Modules.pushforward f).obj M) n).symm ≪≫
    (cohomologyPresheafPushforwardIsoOfIsZeroHigherDirectImage f M hM n).app (.op ⊤) ≪≫
    cohomologyOnTopIso M n

/-- The global comparison is the comparison on the terminal open, transported to global
cohomology. -/
lemma cohomologyPushforwardIsoOfIsZeroHigherDirectImage_hom (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    (cohomologyPushforwardIsoOfIsZeroHigherDirectImage f M hM n).hom =
      (cohomologyOnTopIso ((Scheme.Modules.pushforward f).obj M) n).inv ≫
        (cohomologyPresheafPushforwardIsoOfIsZeroHigherDirectImage f M hM n).hom.app (.op ⊤) ≫
        (cohomologyOnTopIso M n).hom :=
  (rfl)

/-- The inverse global comparison is obtained from the inverse comparison on the terminal open. -/
lemma cohomologyPushforwardIsoOfIsZeroHigherDirectImage_inv (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    (cohomologyPushforwardIsoOfIsZeroHigherDirectImage f M hM n).inv =
      (cohomologyOnTopIso M n).inv ≫
        (cohomologyPresheafPushforwardIsoOfIsZeroHigherDirectImage f M hM n).inv.app (.op ⊤) ≫
        (cohomologyOnTopIso ((Scheme.Modules.pushforward f).obj M) n).hom := by
  exact Category.assoc _ _ _

/-- The acyclic direct-image comparison of global cohomology is natural in coefficients. -/
@[reassoc]
lemma cohomologyPushforwardIsoOfIsZeroHigherDirectImage_naturality {M N : X.Modules} (φ : M ⟶ N)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M))
    (hN : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj N)) (n : ℕ) :
    (cohomologyFunctor Y n).map ((Scheme.Modules.pushforward f).map φ) ≫
      (cohomologyPushforwardIsoOfIsZeroHigherDirectImage f N hN n).hom =
    (cohomologyPushforwardIsoOfIsZeroHigherDirectImage f M hM n).hom ≫
      (cohomologyFunctor X n).map φ := by
  have h₁ := (Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n isTerminalTop).inv.naturality
    ((toSheaf Y).map ((Scheme.Modules.pushforward f).map φ))
  have h₂ := NatTrans.congr_app
    (cohomologyPresheafPushforwardIsoOfIsZeroHigherDirectImage_naturality f φ hM hN n) (.op ⊤)
  have h₃ := (Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n isTerminalTop).hom.naturality
    ((toSheaf X).map φ)
  simp only [NatTrans.comp_app] at h₂
  exact ((CommSq.mk h₁).vert_comp ((CommSq.mk h₂).vert_comp (CommSq.mk h₃))).w

/-- Vanishing of cohomology transfers across an acyclic direct image. -/
theorem subsingleton_cohomology_pushforward_iff_of_isZeroHigherDirectImage (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    Subsingleton (Cohomology ((Scheme.Modules.pushforward f).obj M) n) ↔
      Subsingleton (Cohomology M n) :=
  (cohomologyPushforwardIsoOfIsZeroHigherDirectImage f M hM n).addCommGroupIsoToAddEquiv
    |>.toEquiv.subsingleton_congr

end AlgebraicGeometry.Scheme.Hom
