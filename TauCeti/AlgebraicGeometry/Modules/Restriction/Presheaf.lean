/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Restriction of presheaves of modules along an open immersion

For an open immersion `f : X ⟶ Y`, restriction of presheaves of `𝒪_Y`-modules to `X`
(`AlgebraicGeometry.Scheme.PresheafOfModules.restrictFunctor`) evaluates a presheaf on the images
of the opens of `X`, with scalars through `𝒪_X(V) ≅ 𝒪_Y(f(V))`
(`AlgebraicGeometry.Scheme.PresheafOfModules.restrictFunctor_obj_smul`). It is the presheaf-level
counterpart of Mathlib's restriction of sheaves of modules
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`: forgetting the sheaf condition and then
restricting is restricting and then forgetting
(`AlgebraicGeometry.Scheme.PresheafOfModules.toPresheafOfModulesCompRestrictFunctorIso`).

Restriction of presheaves is exact
(`AlgebraicGeometry.Scheme.PresheafOfModules.preservesHomology_restrictFunctor`): it is a right
adjoint, and it preserves finite colimits because colimits of presheaves of modules are computed
on the underlying presheaves of abelian groups, where restriction is precomposition with the
open-image functor. Exactness is what lets restriction commute with right derived functors with
values in presheaves of modules, such as the presheaf `V ↦ Hⁿ(f⁻¹ V, M)` of higher direct images.
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

variable {f}

/-- The restriction maps of the restriction of `P` are those of `P` between the images. -/
@[simp]
lemma restrictFunctor_obj_map_apply (P : Y.PresheafOfModules) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (y : ((restrictFunctor f).obj P).obj U) :
    ((restrictFunctor f).obj P).map i y = P.map (f.opensFunctor.map i.unop).op y :=
  (rfl)

/-- A function `c` on an open `V` of `X` acts on the restriction of `P` as its image under
`𝒪_X(V) ≅ 𝒪_Y(f(V))` acts on the sections of `P` over `f(V)`. -/
lemma restrictFunctor_obj_smul (P : Y.PresheafOfModules) (V : X.Opens) (c : Γ(X, V))
    (y : ((restrictFunctor f).obj P).obj (op V)) :
    (show X.ringCatSheaf.obj.obj (op V) from c) • y =
      (show Y.ringCatSheaf.obj.obj (op (f ''ᵁ V)) from (f.appIso V).inv c) •
        (show P.obj (op (f ''ᵁ V)) from y) :=
  (rfl)

/-- On sections over `V`, the restriction of a morphism `φ` is `φ` over `f(V)`. -/
@[simp]
lemma restrictFunctor_map_app_apply {P Q : Y.PresheafOfModules} (φ : P ⟶ Q) (V : X.Opensᵒᵖ)
    (y : ((restrictFunctor f).obj P).obj V) :
    ((restrictFunctor f).map φ).app V y = φ.app (op (f.opensFunctor.obj V.unop)) y :=
  (rfl)

variable (f)

instance isRightAdjoint_restrictFunctor : (restrictFunctor f).IsRightAdjoint :=
  _root_.PresheafOfModules.instIsRightAdjointPushforward (F := f.opensFunctor) _

instance additive_restrictFunctor : (restrictFunctor f).Additive :=
  (restrictFunctor f).additive_of_preserves_binary_products

instance preservesFiniteColimits_restrictFunctor :
    PreservesFiniteColimits (restrictFunctor f) := by
  -- On underlying presheaves of abelian groups, restriction is precomposition with the
  -- open-image functor, and forgetting the module structure reflects colimits.
  have : PreservesFiniteColimits (restrictFunctor f ⋙
      _root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj) := by
    have : PreservesFiniteColimits (_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj f.opensFunctor.op) :=
      comp_preservesFiniteColimits _ _
    exact preservesFiniteColimits_of_natIso
      (_root_.PresheafOfModules.pushforwardCompToPresheaf _).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

/-- Restriction of presheaves of modules along an open immersion is exact. -/
instance preservesHomology_restrictFunctor : (restrictFunctor f).PreservesHomology := by
  have h := (restrictFunctor f).exact_tfae.out 4 3
  exact h.1 ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.PresheafOfModules
