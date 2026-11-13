/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
import TauCeti.Algebra.Module.LocalizedModule.Map

/-!
# Restriction of presheaves of modules along an open immersion

For an open immersion `f : X ⟶ Y`, restriction of presheaves of `𝒪_Y`-modules to `X`
(`AlgebraicGeometry.Scheme.PresheafOfModules.restrictFunctor`) evaluates a presheaf on the images
of the opens of `X`, with scalars through `𝒪_X(V) ≅ 𝒪_Y(f(V))`
(`AlgebraicGeometry.Scheme.PresheafOfModules.restrictFunctor_obj_smul`), so morphisms out of a
restriction are linear for these scalars
(`AlgebraicGeometry.Scheme.PresheafOfModules.restrictFunctor_obj_hom_app_smul`). It is the
presheaf-level
counterpart of Mathlib's restriction of sheaves of modules
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`: forgetting the sheaf condition and then
restricting is restricting and then forgetting
(`AlgebraicGeometry.Scheme.PresheafOfModules.toPresheafOfModulesCompRestrictFunctorIso`).

Restriction to an open subscheme `W` of `Y` turns a function `s` on `W` into a global function of
`W`. Whether the restriction of a presheaf of modules from `W` to the basic open `D(s)` is the
localization at `s` can therefore be checked on its restriction to `W`, where the basic open of the
global function `s` is involved
(`Scheme.PresheafOfModules.isLocalizedModule_map_basicOpen_of_restrictFunctor_obj_iso`).

Restriction of presheaves is exact: as a pushforward of presheaves of modules it preserves finite
limits and finite colimits
(`AlgebraicGeometry.Scheme.PresheafOfModules.preservesFiniteLimits_restrictFunctor` and
`AlgebraicGeometry.Scheme.PresheafOfModules.preservesFiniteColimits_restrictFunctor`, from
`TauCeti.PresheafOfModules.preservesFiniteLimits_pushforward` and
`TauCeti.PresheafOfModules.preservesFiniteColimits_pushforward`), so it preserves homology by
Mathlib's `CategoryTheory.Functor.preservesHomologyOfExact`. Exactness is what lets restriction
commute with right derived functors with values in presheaves of modules, such as the presheaf
`V ↦ Hⁿ(f⁻¹ V, M)` of higher direct images.
-/

public section

open CategoryTheory Limits Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.PresheafOfModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Restriction of presheaves of `𝒪_Y`-modules along an open immersion `f : X ⟶ Y`: the sections
over an open `V` of `X` are the sections over its image `f(V)`, with scalars through
`𝒪_X(V) ≅ 𝒪_Y(f(V))`. -/
-- Exposed so that the sections of a restriction are those of the original presheaf over the
-- images, as the statements of the characterizing lemmas below require.
@[expose]
def restrictFunctor : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  _root_.PresheafOfModules.pushforward (F := f.opensFunctor)
    (Scheme.Modules.restrictRingCatSheafHom f).hom

/-- Forgetting the sheaf condition commutes with restriction along an open immersion. -/
def toPresheafOfModulesCompRestrictFunctorIso :
    Scheme.Modules.toPresheafOfModules Y ⋙ restrictFunctor f ≅
      Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheafOfModules X :=
  -- Restriction of sheaves of modules is defined as the pushforward of the underlying presheaves.
  Iso.refl _

/-- On sections, the comparison `toPresheafOfModulesCompRestrictFunctorIso` is the identity. -/
@[simp]
lemma toPresheafOfModulesCompRestrictFunctorIso_hom_app_app_apply (M : Y.Modules) (V : X.Opensᵒᵖ)
    (x : ((restrictFunctor f).obj ((Scheme.Modules.toPresheafOfModules Y).obj M)).obj V) :
    dsimp% only [Functor.comp_obj]
      (((toPresheafOfModulesCompRestrictFunctorIso f).hom.app M).app V) x = x :=
  (rfl)

/-- On sections, the inverse of `toPresheafOfModulesCompRestrictFunctorIso` is the identity. -/
@[simp]
lemma toPresheafOfModulesCompRestrictFunctorIso_inv_app_app_apply (M : Y.Modules) (V : X.Opensᵒᵖ)
    (x : ((Scheme.Modules.toPresheafOfModules X).obj
      ((Scheme.Modules.restrictFunctor f).obj M)).obj V) :
    dsimp% only [Functor.comp_obj]
      (((toPresheafOfModulesCompRestrictFunctorIso f).inv.app M).app V) x = x :=
  (rfl)

variable {f}

/-- The restriction maps of the restriction of `P` are those of `P` between the images. -/
@[simp]
lemma restrictFunctor_obj_map_apply (P : Y.PresheafOfModules) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (y : ((restrictFunctor f).obj P).obj U) :
    ((restrictFunctor f).obj P).map i y = P.map (f.opensFunctor.map i.unop).op y :=
  (rfl)

-- The `show`s identify `Γ(X, V)` and `Γ(Y, f ''ᵁ V)` with the rings `ringCatSheaf.obj.obj` acting
-- on the sections, and a section of the restriction with the section of `P` over the image.
/-- A function `c` on an open `V` of `X` acts on the restriction of `P` as its image under
`𝒪_X(V) ≅ 𝒪_Y(f(V))` acts on the sections of `P` over `f(V)`. -/
lemma restrictFunctor_obj_smul (P : Y.PresheafOfModules) (V : X.Opens) (c : Γ(X, V))
    (y : ((restrictFunctor f).obj P).obj (op V)) :
    (show X.ringCatSheaf.obj.obj (op V) from c) • y =
      (show Y.ringCatSheaf.obj.obj (op (f ''ᵁ V)) from (f.appIso V).inv c) •
        (show P.obj (op (f ''ᵁ V)) from y) :=
  (rfl)

-- As in `restrictFunctor_obj_smul`, the `show`s identify the functions with the rings acting on
-- the sections.
/-- A morphism `φ` out of the restriction of `P` is linear for the functions `c` on opens `V` of
`X`, which act on the sections of `P` over `f(V)` through `𝒪_X(V) ≅ 𝒪_Y(f(V))`. -/
lemma restrictFunctor_obj_hom_app_smul {P : Y.PresheafOfModules} {Q : X.PresheafOfModules}
    (φ : (restrictFunctor f).obj P ⟶ Q) (V : X.Opens) (c : Γ(X, V))
    (y : P.obj (op (f ''ᵁ V))) :
    φ.app (op V) ((show Y.ringCatSheaf.obj.obj (op (f ''ᵁ V)) from (f.appIso V).inv c) • y) =
      (show X.ringCatSheaf.obj.obj (op V) from c) • φ.app (op V) y :=
  (congrArg _ (restrictFunctor_obj_smul P V c y).symm).trans ((φ.app (op V)).hom.map_smul c y)

/-- On sections over `V`, the restriction of a morphism `φ` is `φ` over `f(V)`. -/
@[simp]
lemma restrictFunctor_map_app_apply {P Q : Y.PresheafOfModules} (φ : P ⟶ Q) (V : X.Opensᵒᵖ)
    (y : ((restrictFunctor f).obj P).obj V) :
    ((restrictFunctor f).map φ).app V y = φ.app (op (f.opensFunctor.obj V.unop)) y :=
  (rfl)

variable (f)

instance isRightAdjoint_restrictFunctor : (restrictFunctor f).IsRightAdjoint :=
  _root_.PresheafOfModules.instIsRightAdjointPushforward (F := f.opensFunctor) _

-- As for `isRightAdjoint_restrictFunctor`, the open-image functor is passed explicitly, since the
-- coefficient morphism hides it from instance search.
instance additive_restrictFunctor : (restrictFunctor f).Additive :=
  TauCeti.PresheafOfModules.additive_pushforward (F := f.opensFunctor) _

instance preservesFiniteLimits_restrictFunctor : PreservesFiniteLimits (restrictFunctor f) :=
  TauCeti.PresheafOfModules.preservesFiniteLimits_pushforward (F := f.opensFunctor) _

instance preservesFiniteColimits_restrictFunctor :
    PreservesFiniteColimits (restrictFunctor f) :=
  TauCeti.PresheafOfModules.preservesFiniteColimits_pushforward (F := f.opensFunctor) _

/-- **Localization of restriction maps can be checked on an open subscheme.** Let `W` be an open
of `Y`, `s` a function on `W` and `e` an isomorphism from the restriction of `P` to `W` to a
presheaf of modules `Q` on `W`. If the restriction of `Q` from `W` to the basic open of `s`, a
global function of `W`, is the localization at the powers of `s`, then so is the restriction of
`P` from `W` to `D(s)`. -/
theorem isLocalizedModule_map_basicOpen_of_restrictFunctor_obj_iso {W : Y.Opens}
    {P : Y.PresheafOfModules} {Q : W.toScheme.PresheafOfModules}
    (e : (restrictFunctor W.ι).obj P ≅ Q) (s : Γ(Y, W))
    (h : IsLocalizedModule (.powers (W.topIso.inv s))
      (PresheafOfModulesOfCommRing.map (R := W.toScheme.presheaf) Q
        (homOfLE (W.toScheme.basicOpen_le (W.topIso.inv s))).op).hom) :
    IsLocalizedModule (.powers s) (PresheafOfModulesOfCommRing.map (R := Y.presheaf) P
      (homOfLE (Y.basicOpen_le s)).op).hom := by
  let s' : Γ(W, ⊤) := W.topIso.inv s
  have hs : W.ι ''ᵁ W.toScheme.basicOpen s' = Y.basicOpen s :=
    Scheme.Opens.ι_image_basicOpen_topIso_inv W s
  have : IsLocalizedModule ((Submonoid.powers s).map W.topIso.inv.hom)
      (PresheafOfModulesOfCommRing.map (R := W.toScheme.presheaf) Q
        (homOfLE (W.toScheme.basicOpen_le s')).op).hom := by
    rwa [Submonoid.map_powers]
  have : IsIso (e.hom.app (.op ⊤)) := inferInstanceAs
    (IsIso ((_root_.PresheafOfModules.evaluation _ (.op ⊤)).map e.hom))
  have : IsIso (e.hom.app (.op (W.toScheme.basicOpen s'))) := inferInstanceAs
    (IsIso ((_root_.PresheafOfModules.evaluation _ (.op (W.toScheme.basicOpen s'))).map e.hom))
  -- `e.hom` is linear for the functions on opens of `W`, which act on the restriction of `P` as on
  -- the sections over their images, since `W.ι.appIso` is the identity
  have hsmul (V : W.toScheme.Opens) (c : Γ(W, V)) (y : P.obj (.op (W.ι ''ᵁ V))) :
      e.hom.app (.op V) ((show Y.ringCatSheaf.obj.obj (.op (W.ι ''ᵁ V)) from c) • y) =
        (show W.toScheme.ringCatSheaf.obj.obj (.op V) from c) • e.hom.app (.op V) y := by
    have h := restrictFunctor_obj_hom_app_smul e.hom V c y
    rwa [Scheme.Opens.ι_appIso, Iso.refl_inv] at h
  -- Compare `W` and `D(s)` with the images of `⊤` and `D(s')` under the inclusion of `W`, then
  -- pass to `Q` along `e`.
  refine IsLocalizedModule.of_bijective_semilinearMap (σ := W.topIso.inv.hom) (.powers s)
    (PresheafOfModulesOfCommRing.map (R := Y.presheaf) P (homOfLE (Y.basicOpen_le s)).op).hom
    (PresheafOfModulesOfCommRing.map (R := W.toScheme.presheaf) Q
        (homOfLE (W.toScheme.basicOpen_le s')).op).hom
    { (e.hom.app (.op ⊤)).hom.toAddMonoidHom.comp
        (P.map (eqToHom W.ι_image_top).op).hom.toAddMonoidHom with
      map_smul' := fun r x ↦ ?_ }
    { (e.hom.app (.op (W.toScheme.basicOpen s'))).hom.toAddMonoidHom.comp
        (P.map (eqToHom hs).op).hom.toAddMonoidHom with
      map_smul' := fun r x ↦ ?_ }
    ((ConcreteCategory.bijective_of_isIso (e.hom.app (.op ⊤))).comp
      (ConcreteCategory.bijective_of_isIso (P.presheaf.map (eqToHom W.ι_image_top).op)))
    ((ConcreteCategory.bijective_of_isIso (e.hom.app (.op (W.toScheme.basicOpen s')))).comp
      (ConcreteCategory.bijective_of_isIso (P.presheaf.map (eqToHom hs).op))) fun x ↦ ?_
  · refine Eq.trans (congrArg (e.hom.app (.op ⊤)) ?_)
      (hsmul ⊤ (W.topIso.inv r) _)
    -- `W.topIso.inv` is the restriction of functions from `W` to `W.ι ''ᵁ ⊤`
    exact (P.map (eqToHom W.ι_image_top).op).hom.map_smul r x
  · refine Eq.trans (congrArg (e.hom.app (.op (W.toScheme.basicOpen s'))) ?_)
      (hsmul _ (W.toScheme.presheaf.map (homOfLE le_top).op (W.topIso.inv r)) _)
    refine ((P.map (eqToHom hs).op).hom.map_smul _ x).trans ?_
    -- write the action through restriction of scalars as the action of the restricted function;
    -- `erw` because the restricted function lies in `Γ(Y, D(s))`, which is only definitionally the
    -- ring `Y.ringCatSheaf.obj.obj` acting on the sections, so `rw` gives an ill-typed motive
    erw [ModuleCat.restrictScalars.smul_def]
    congr 1
    -- both scalars are restrictions of `r` from `W` to `W.ι ''ᵁ D(s')`
    have key : ∀ {U₁ U₂ : Y.Opens} (i₁ : op W ⟶ op U₁) (j₁ : op U₁ ⟶ op (W.ι ''ᵁ
        W.toScheme.basicOpen s')) (i₂ : op W ⟶ op U₂)
        (j₂ : op U₂ ⟶ op (W.ι ''ᵁ W.toScheme.basicOpen s')),
        Y.presheaf.map j₁ (Y.presheaf.map i₁ r) = Y.presheaf.map j₂ (Y.presheaf.map i₂ r) := by
      intro U₁ U₂ i₁ j₁ i₂ j₂
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp]
      rfl
    exact key _ _ _ _
  · have h := _root_.PresheafOfModules.naturality_apply e.hom
      (homOfLE (W.toScheme.basicOpen_le s')).op (P.map (eqToHom W.ι_image_top).op x)
    refine Eq.trans (congrArg (fun y ↦ e.hom.app (.op (W.toScheme.basicOpen s')) y) ?_) h
    -- both sides restrict `x` from `W` to `W.ι ''ᵁ D(s')`
    have h3 : P.map (eqToHom hs).op (P.map (homOfLE (Y.basicOpen_le s)).op x) =
        P.map (W.ι.opensFunctor.map (homOfLE (W.toScheme.basicOpen_le s'))).op
          (P.map (eqToHom W.ι_image_top).op x) := by
      rw [← _root_.PresheafOfModules.map_comp_apply, ← _root_.PresheafOfModules.map_comp_apply]
      exact _root_.PresheafOfModules.congr_map_apply P (Subsingleton.elim _ _) x
    exact h3.trans (restrictFunctor_obj_map_apply P _ _).symm

end AlgebraicGeometry.Scheme.PresheafOfModules
