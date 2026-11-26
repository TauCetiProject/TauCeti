/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic

/-!
# Modules over a preadditive category

Let `C` be a preadditive category. A `C`-module is a contravariant additive functor
`Cᵒᵖ ⥤ AddCommGrpCat`, and `TauCeti.ModCat C := Cᵒᵖ ⥤+ AddCommGrpCat.{w}` is the category of
`C`-modules, the full subcategory of additive functors in `Cᵒᵖ ⥤ AddCommGrpCat.{w}`. Covariant
additive functors `C ⥤ AddCommGrpCat` are the objects of `ModCat Cᵒᵖ`. For a ring `A`, the category
`ModCat (SingleObj Aᵐᵒᵖ)` is the category of left `A`-modules.

Kernels, cokernels and (co)limits in a functor category are computed pointwise, so a (co)limit
of additive functors is again additive. Hence the additive functors `D ⥤ A` into a preadditive
category `A` contain zero and are closed under kernels, cokernels, finite products, and all
limits and colimits that exist in `A`. Mathlib's `CategoryTheory/Abelian/Subcategory.lean` then
makes `ModCat C` abelian, and it has every shape of colimit that `AddCommGrpCat.{w}` has.

The representable functors `Hom(-, X)` form the Yoneda embedding `ModCat.yoneda : C ⥤ ModCat C`,
and they are projective by the Yoneda lemma. When `D` is `R`-linear, so is the category
`D ⥤+ A` of additive functors into any preadditive `A`, with `r ∈ R` acting on `φ : F ⟶ G` by
`φ ≫ G(r • 𝟙)` ([Mitchell, §11]); in particular `ModCat D` is `R`-linear. Finally, finitely
presented functors are additive, so `mod C` is a full subcategory of `ModCat C`.

## Main definitions

* `TauCeti.ModCat C`: the category `Cᵒᵖ ⥤+ AddCommGrpCat.{w}` of `C`-modules.
* `TauCeti.ModCat.yoneda C : C ⥤ ModCat C`: the Yoneda embedding `X ↦ Hom(-, X)`.
* `TauCeti.AdditiveFunctor.smulEnd R r G : G ⟶ G`: the action of `r ∈ R` on an additive functor
  `G` out of an `R`-linear category.
* `TauCeti.AdditiveFunctor.sourceLinear R : Linear R (D ⥤+ A)`: the `R`-linear structure induced
  by an `R`-linear source.
* `TauCeti.ModCat.ofFinitelyPresented C`: the fully faithful inclusion `mod C ⥤ ModCat C`.

## Main results

* `TauCeti.additiveFunctor_isClosedUnderLimitsOfShape`,
  `TauCeti.additiveFunctor_isClosedUnderColimitsOfShape`: additive functors are closed under the
  limits and colimits of the target, together with instances for zero, kernels, cokernels and
  finite products.
* `Abelian (ModCat C)` and `HasColimitsOfShape J (ModCat C)`, found by instance inference from
  the closure instances and Mathlib's full-subcategory instances.
* `Projective ((ModCat.yoneda C).obj X)`: representable modules are projective.
* `Linear R (D ⥤+ AddCommGrpCat)` for an `R`-linear preadditive category `D`; specializing `D`
  to an opposite category gives `Linear R (ModCat D)`.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §§3, 11.
-/

public section

universe w v u

open CategoryTheory Limits Opposite ZeroObject

namespace TauCeti

section Closure

variable {D : Type*} [Category* D] [Preadditive D] {A : Type*} [Category* A] [Preadditive A]

/-- A limit of additive functors is additive: limits in `D ⥤ A` are computed pointwise, so
`F.map (f + g)` is detected by its composites with the projections of the pointwise limit. -/
instance additiveFunctor_isClosedUnderLimitsOfShape (J : Type*) [Category* J]
    [HasLimitsOfShape J A] : (additiveFunctor D A).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro F ⟨h⟩
    refine ⟨fun {X Y f g} ↦ ?_⟩
    refine (isLimitOfPreserves ((evaluation D A).obj Y) h.isLimit).hom_ext fun j ↦ ?_
    have : (h.diag.obj j).Additive := h.prop_diag_obj j
    have hn (u : X ⟶ Y) : F.map u ≫ (h.π.app j).app Y = (h.π.app j).app X ≫ (h.diag.obj j).map u :=
      (h.π.app j).naturality u
    simp only [Functor.mapCone_π_app, evaluation_obj_map, Preadditive.add_comp, hn,
      Functor.map_add, Preadditive.comp_add]

/-- A colimit of additive functors is additive: colimits in `D ⥤ A` are computed pointwise, so
`F.map (f + g)` is detected by its composites with the injections of the pointwise colimit. -/
instance additiveFunctor_isClosedUnderColimitsOfShape (J : Type*) [Category* J]
    [HasColimitsOfShape J A] : (additiveFunctor D A).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro F ⟨h⟩
    refine ⟨fun {X Y f g} ↦ ?_⟩
    refine (isColimitOfPreserves ((evaluation D A).obj X) h.isColimit).hom_ext fun j ↦ ?_
    have : (h.diag.obj j).Additive := h.prop_diag_obj j
    have hn (u : X ⟶ Y) : (h.ι.app j).app X ≫ F.map u = (h.diag.obj j).map u ≫ (h.ι.app j).app Y :=
      ((h.ι.app j).naturality u).symm
    simp only [Functor.mapCocone_ι_app, evaluation_obj_map, Preadditive.comp_add, hn,
      Functor.map_add, Preadditive.add_comp]

/-- The zero functor is additive. -/
instance [HasZeroObject A] : (additiveFunctor D A).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, (inferInstance : (0 : D ⥤ A).Additive)⟩

/-- A kernel of a morphism of additive functors is additive. -/
instance [HasEqualizers A] : (additiveFunctor D A).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (additiveFunctor D A).prop_of_isLimit hk (by rintro (_ | _) <;> assumption)

/-- A cokernel of a morphism of additive functors is additive. -/
instance [HasCoequalizers A] : (additiveFunctor D A).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (additiveFunctor D A).prop_of_isColimit hk (by rintro (_ | _) <;> assumption)

/-- A finite product of additive functors is additive. -/
instance [HasFiniteProducts A] : (additiveFunctor D A).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape _ _ := inferInstance

end Closure

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The category `Mod C` of `C`-modules: the contravariant additive functors
`Cᵒᵖ ⥤+ AddCommGrpCat.{w}`. Covariant additive functors on `C` are the objects of `ModCat Cᵒᵖ`. -/
abbrev ModCat := Cᵒᵖ ⥤+ AddCommGrpCat.{w}

/-- `Mod C` is abelian: instance inference finds this from the closure instances above. -/
noncomputable example : Abelian (ModCat.{w} C) := inferInstance

/-- `Mod C` has every shape of colimit that `AddCommGrpCat.{w}` has, again by inference. -/
example {J : Type*} [Category J] [HasColimitsOfShape J AddCommGrpCat.{w}] :
    HasColimitsOfShape J (ModCat.{w} C) :=
  inferInstance

namespace ModCat

/-- The Yoneda embedding `X ↦ Hom(-, X)` of `C` into `Mod C`: the lift of `preadditiveYoneda`
through the full subcategory of additive functors. It is fully faithful by the `ObjectProperty.lift`
instances, and `ObjectProperty.liftCompιIso` recovers `preadditiveYoneda`. -/
abbrev yoneda : C ⥤ ModCat.{v} C :=
  ObjectProperty.lift _ preadditiveYoneda fun _ ↦ (additiveFunctor_iff _).2 inferInstance

/-- **Representable modules are projective.** A morphism `Hom(-, X) ⟶ G` is an element of
`G(X)` by Yoneda, and it lifts along an epimorphism `F ⟶ G`, which is surjective at `X`. -/
instance (X : C) : Projective ((yoneda C).obj X) where
  factors {E F} g π _ := by
    have := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).preservesEpimorphisms_ι_of_isNormalMonoCategory
    have : Epi π.hom := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι.map_epi π
    obtain ⟨s, hs⟩ := exists_comp_eq_preadditiveYoneda_obj_of_epi π.hom g.hom
    exact ⟨ObjectProperty.homMk s, ObjectProperty.hom_ext _ hs⟩

end ModCat

section Linear

variable {D : Type*} [Category* D] [Preadditive D] {A : Type*} [Category* A] [Preadditive A]
  (R : Type*) [Semiring R] [Linear R D]

namespace AdditiveFunctor

/-- The action of `r ∈ R` on an additive functor `G` out of an `R`-linear category: the
endomorphism of `G` whose component at `X` is `G(r • 𝟙 X)`. -/
def smulEnd (r : R) (G : D ⥤+ A) : G ⟶ G :=
  ObjectProperty.homMk
    { app X := G.obj.map (r • 𝟙 X)
      naturality X Y f := by rw [← G.obj.map_comp, ← G.obj.map_comp, Linear.smul_comp,
        Linear.comp_smul, Category.id_comp, Category.comp_id] }

/-- The component of `smulEnd R r G` at `X` is `G(r • 𝟙 X)`. -/
@[simp]
theorem smulEnd_hom_app (r : R) (G : D ⥤+ A) (X : D) :
    (smulEnd R r G).hom.app X = G.obj.map (r • 𝟙 X) := by
  simp [smulEnd]

/-- The action of `r ∈ R` commutes with every morphism of additive functors. -/
@[reassoc]
theorem comp_smulEnd (r : R) {F G : D ⥤+ A} (φ : F ⟶ G) :
    φ ≫ smulEnd R r G = smulEnd R r F ≫ φ := by
  ext X : 3
  exact (φ.hom.naturality _).symm

/-- The unit of `R` acts as the identity. -/
@[simp]
theorem smulEnd_one (G : D ⥤+ A) : smulEnd R 1 G = 𝟙 G := by
  ext X : 3
  simp

/-- The action of `r * s` is the action of `s` followed by the action of `r`. -/
theorem smulEnd_mul (r s : R) (G : D ⥤+ A) :
    smulEnd R (r * s) G = smulEnd R s G ≫ smulEnd R r G := by
  ext X : 3
  simp [← Functor.map_comp, mul_smul]

/-- The action is additive in the scalar. -/
theorem smulEnd_add (r s : R) (G : D ⥤+ A) :
    smulEnd R (r + s) G = smulEnd R r G + smulEnd R s G := by
  have h := (AdditiveFunctor.forget D A).map_add (f := smulEnd R r G) (g := smulEnd R s G)
  simp only [AdditiveFunctor.forget_map] at h
  ext X : 3
  simp [h, add_smul, Functor.map_add]

/-- The zero scalar acts as zero. -/
@[simp]
theorem smulEnd_zero (G : D ⥤+ A) : smulEnd R 0 G = 0 := by
  ext X : 3
  simp

/-- The `R`-linear structure on `D ⥤+ A` coming from the `R`-linear source `D`: `r ∈ R` acts on
`φ : F ⟶ G` by `φ ≫ smulEnd R r G`, with components `φ_X ≫ G(r • 𝟙 X)` ([Mitchell, §11]).

It is not a global instance: when `A` is `R`-linear too, Mathlib's `functorCategoryLinear` and
`Linear.fullSubcategory` give `D ⥤+ A` the pointwise `R`-linear structure of the target, which
differs from this one on functors that are additive but not `R`-linear. -/
@[instance_reducible]
def sourceLinear : Linear R (D ⥤+ A) where
  homModule _ G :=
    { smul r φ := φ ≫ smulEnd R r G
      one_smul φ := (congrArg (φ ≫ ·) (smulEnd_one R G)).trans (Category.comp_id φ)
      mul_smul r s φ := (congrArg (φ ≫ ·) (smulEnd_mul R r s G)).trans
        (Category.assoc _ _ _).symm
      smul_zero _ := zero_comp
      smul_add _ _ _ := Preadditive.add_comp _ _ _ _ _ _
      add_smul r s φ := (congrArg (φ ≫ ·) (smulEnd_add R r s G)).trans
        (Preadditive.comp_add _ _ _ _ _ _)
      zero_smul φ := (congrArg (φ ≫ ·) (smulEnd_zero R G)).trans comp_zero }
  smul_comp _ _ _ r φ ψ :=
    (Category.assoc _ _ _).trans <| ((congrArg (φ ≫ ·) (comp_smulEnd R r ψ)).symm).trans
      (Category.assoc _ _ _).symm
  comp_smul _ _ _ _ _ _ := (Category.assoc _ _ _).symm

attribute [local instance] sourceLinear

/-- In `sourceLinear R`, the scalar `r` acts on `φ : F ⟶ G` by composing with `smulEnd R r G`. -/
theorem smul_eq_comp_smulEnd (r : R) {F G : D ⥤+ A} (φ : F ⟶ G) :
    r • φ = φ ≫ smulEnd R r G := by
  unfold sourceLinear
  rfl

/-- In `sourceLinear R`, the components of `r • φ` are `φ_X ≫ G(r • 𝟙 X)`. -/
@[simp]
theorem smul_hom_app (r : R) {F G : D ⥤+ A} (φ : F ⟶ G) (X : D) :
    (r • φ).hom.app X = φ.hom.app X ≫ G.obj.map (r • 𝟙 X) := by
  simp [smul_eq_comp_smulEnd]

end AdditiveFunctor

/-- **Additive functors into abelian groups out of an `R`-linear category are `R`-linear**, with
the structure `AdditiveFunctor.sourceLinear R`. The target `AddCommGrpCat` is linear only over
`ℕ` and `ℤ`, where the two actions agree, so this instance does not compete with the pointwise
structure. -/
instance AdditiveFunctor.linearAddCommGrpCat : Linear R (D ⥤+ AddCommGrpCat.{w}) :=
  AdditiveFunctor.sourceLinear R

/-- **`Mod D` is `R`-linear** when `D` is, by specializing the instance above to the source
`Dᵒᵖ`. -/
example : Linear R (ModCat.{w} D) := inferInstance

end Linear

/-- Finitely presented functors are additive, so `mod C` is contained in `Mod C`. -/
theorem isFinitelyPresentedFunctor_le_additiveFunctor :
    isFinitelyPresentedFunctor C ≤ additiveFunctor Cᵒᵖ AddCommGrpCat.{v} :=
  fun _ hF ↦ hF.additive

namespace ModCat

/-- The inclusion `mod C ⥤ Mod C` of finitely presented functors into all modules. It is fully
faithful by `ObjectProperty.fullyFaithfulιOfLE`, and `ObjectProperty.liftCompιOfLEIso` identifies
`modYoneda ⋙ ofFinitelyPresented C` with `ModCat.yoneda C`. -/
abbrev ofFinitelyPresented : (isFinitelyPresentedFunctor C).FullSubcategory ⥤ ModCat.{v} C :=
  ObjectProperty.ιOfLE (isFinitelyPresentedFunctor_le_additiveFunctor C)

end ModCat

end TauCeti
