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
and they are projective by the Yoneda lemma. When `D` is `R`-linear, `ModCat D` is `R`-linear,
with `r ∈ R` acting on `φ : F ⟶ G` by `φ ≫ G(r • 𝟙)` ([Mitchell, §11]). Finally, finitely
presented functors are additive, so `mod C` is a full subcategory of `ModCat C`.

## Main definitions

* `TauCeti.ModCat C`: the category `Cᵒᵖ ⥤+ AddCommGrpCat.{w}` of `C`-modules.
* `TauCeti.ModCat.yoneda C : C ⥤ ModCat C`: the Yoneda embedding `X ↦ Hom(-, X)`.
* `TauCeti.ModCat.smulEnd R r G : G ⟶ G`: the action of `r ∈ R` on an `R`-linear module `G`.
* `TauCeti.ModCat.ofFinitelyPresented C`: the fully faithful inclusion `mod C ⥤ ModCat C`.

## Main results

* `TauCeti.additiveFunctor_isClosedUnderLimitsOfShape`,
  `TauCeti.additiveFunctor_isClosedUnderColimitsOfShape`: additive functors are closed under the
  limits and colimits of the target, together with instances for zero, kernels, cokernels and
  finite products.
* `Abelian (ModCat C)` and `HasColimitsOfShape J (ModCat C)`.
* `Projective ((ModCat.yoneda C).obj X)`: representable modules are projective.
* `Linear R (ModCat D)` for an `R`-linear preadditive category `D`.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §§3, 11.
-/

@[expose] public section

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

/-- `Mod C` is abelian, as a full subcategory of `Cᵒᵖ ⥤ AddCommGrpCat` containing zero and closed
under kernels, cokernels and finite products. -/
noncomputable instance : Abelian (ModCat.{w} C) := inferInstance

/-- `Mod C` has every shape of colimit that `AddCommGrpCat.{w}` has, computed pointwise. -/
instance (priority := high) {J : Type*} [Category J] [HasColimitsOfShape J AddCommGrpCat.{w}] :
    HasColimitsOfShape J (ModCat.{w} C) :=
  hasColimitsOfShape_of_closedUnderColimits _ _

namespace ModCat

/-- The Yoneda embedding `X ↦ Hom(-, X)` of `C` into `Mod C`. -/
def yoneda : C ⥤ ModCat.{v} C :=
  ObjectProperty.lift _ preadditiveYoneda fun X ↦
    (inferInstance : (preadditiveYoneda.obj X).Additive)

/-- The underlying functor of `(ModCat.yoneda C).obj X` is `Hom(-, X)`. -/
@[simp]
theorem yoneda_obj_obj (X : C) : ((yoneda C).obj X).obj = preadditiveYoneda.obj X :=
  rfl

/-- The underlying natural transformation of `(ModCat.yoneda C).map f` is `Hom(-, f)`. -/
@[simp]
theorem yoneda_map_hom {X Y : C} (f : X ⟶ Y) : ((yoneda C).map f).hom = preadditiveYoneda.map f :=
  rfl

/-- `ModCat.yoneda C` followed by the forgetful functor `Mod C ⥤ (Cᵒᵖ ⥤ AddCommGrpCat)` is
`preadditiveYoneda`. -/
def yonedaCompιIso : yoneda C ⋙ (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι ≅ preadditiveYoneda :=
  Iso.refl _

instance : (yoneda C).Full := Functor.Full.of_comp_faithful_iso (yonedaCompιIso C)

instance : (yoneda C).Faithful := Functor.Faithful.of_comp_iso (yonedaCompιIso C)

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

variable {D : Type u} [Category.{v} D] [Preadditive D] (R : Type*) [Semiring R] [Linear R D]

namespace ModCat

/-- The action of `r ∈ R` on a module `G` over an `R`-linear category: the endomorphism of `G`
whose component at `c` is `G(r • 𝟙 c)`. -/
def smulEnd (r : R) (G : ModCat.{w} D) : G ⟶ G :=
  ObjectProperty.homMk
    { app c := G.obj.map (r • 𝟙 c.unop).op
      naturality c c' f := by
        rw [← G.obj.map_comp, ← G.obj.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        simp }

/-- The component of `smulEnd R r G` at `c` is `G(r • 𝟙 c)`. -/
@[simp]
theorem smulEnd_hom_app (r : R) (G : ModCat.{w} D) (c : Dᵒᵖ) :
    (smulEnd R r G).hom.app c = G.obj.map (r • 𝟙 c.unop).op :=
  rfl

/-- The action of `r ∈ R` commutes with every morphism of modules. -/
@[reassoc]
theorem comp_smulEnd (r : R) {F G : ModCat.{w} D} (φ : F ⟶ G) :
    φ ≫ smulEnd R r G = smulEnd R r F ≫ φ := by
  ext c : 3
  exact (φ.hom.naturality _).symm

/-- The unit of `R` acts as the identity. -/
@[simp]
theorem smulEnd_one (G : ModCat.{w} D) : smulEnd R 1 G = 𝟙 G := by
  ext c : 3
  simp

/-- The action of `r * s` is the action of `s` followed by the action of `r`. -/
theorem smulEnd_mul (r s : R) (G : ModCat.{w} D) :
    smulEnd R (r * s) G = smulEnd R s G ≫ smulEnd R r G := by
  ext c : 3
  simp [← Functor.map_comp, mul_smul]

/-- The action is additive in the scalar. -/
theorem smulEnd_add (r s : R) (G : ModCat.{w} D) :
    smulEnd R (r + s) G = smulEnd R r G + smulEnd R s G := by
  ext c : 3
  change _ = ((smulEnd R r G).hom + (smulEnd R s G).hom).app c
  simp [add_smul, op_add, Functor.map_add]

/-- The zero scalar acts as zero. -/
@[simp]
theorem smulEnd_zero (G : ModCat.{w} D) : smulEnd R 0 G = 0 := by
  ext c : 3
  simp

end ModCat

/-- **`Mod D` is `R`-linear** when `D` is: `r ∈ R` acts on `φ : F ⟶ G` by `φ ≫ G(r • 𝟙)`. -/
instance : Linear R (ModCat.{w} D) where
  homModule F G :=
    { smul r φ := φ ≫ ModCat.smulEnd R r G
      one_smul φ := by
        change φ ≫ _ = φ
        simp
      mul_smul r s φ := by
        change φ ≫ _ = (φ ≫ _) ≫ _
        rw [ModCat.smulEnd_mul, Category.assoc]
      smul_zero r := zero_comp
      smul_add r φ ψ := Preadditive.add_comp _ _ _ _ _ _
      add_smul r s φ := by
        change φ ≫ _ = φ ≫ _ + φ ≫ _
        rw [ModCat.smulEnd_add, Preadditive.comp_add]
      zero_smul φ := by
        change φ ≫ _ = 0
        simp }
  smul_comp F G H r φ ψ := by
    change (φ ≫ _) ≫ ψ = (φ ≫ ψ) ≫ _
    rw [Category.assoc, ← ModCat.comp_smulEnd, Category.assoc]
  comp_smul F G H φ r ψ := (Category.assoc _ _ _).symm

/-- The components of `r • φ` are `φ_c ≫ G(r • 𝟙 c)`. -/
@[simp]
theorem ModCat.smul_hom_app (r : R) {F G : ModCat.{w} D} (φ : F ⟶ G) (c : Dᵒᵖ) :
    (r • φ).hom.app c = φ.hom.app c ≫ G.obj.map (r • 𝟙 c.unop).op :=
  rfl

end Linear

/-- Finitely presented functors are additive, so `mod C` is contained in `Mod C`. -/
theorem isFinitelyPresentedFunctor_le_additiveFunctor :
    isFinitelyPresentedFunctor C ≤ additiveFunctor Cᵒᵖ AddCommGrpCat.{v} :=
  fun _ hF ↦ hF.additive

namespace ModCat

/-- The inclusion `mod C ⥤ Mod C` of finitely presented functors into all modules. -/
abbrev ofFinitelyPresented : (isFinitelyPresentedFunctor C).FullSubcategory ⥤ ModCat.{v} C :=
  ObjectProperty.ιOfLE (isFinitelyPresentedFunctor_le_additiveFunctor C)

/-- The inclusion `mod C ⥤ Mod C` is fully faithful. -/
def fullyFaithfulOfFinitelyPresented : (ofFinitelyPresented C).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

/-- The inclusion `mod C ⥤ Mod C` is compatible with the inclusions of both into
`Cᵒᵖ ⥤ AddCommGrpCat`. -/
def ofFinitelyPresentedCompιIso :
    ofFinitelyPresented C ⋙ (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι ≅
      (isFinitelyPresentedFunctor C).ι :=
  Iso.refl _

/-- The Yoneda embedding into `mod C` followed by `mod C ⥤ Mod C` is `ModCat.yoneda C`. -/
def modYonedaCompOfFinitelyPresentedIso : modYoneda ⋙ ofFinitelyPresented C ≅ yoneda C :=
  Iso.refl _

end ModCat

end TauCeti
