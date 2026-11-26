/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Center.Linear
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
category `A` contain zero and are closed under kernels, cokernels, and all limits and colimits
that exist in `A`. They are also closed under every finite product that exists in `D ⥤ A`, since
such a product is a biproduct and the additive evaluation functors preserve it. Mathlib's
`CategoryTheory/Abelian/Subcategory.lean` then makes `ModCat C` abelian, and it has every shape of
colimit that `AddCommGrpCat.{w}` has.

The representable functors `Hom(-, X)` form the Yoneda embedding `ModCat.yoneda : C ⥤ ModCat C`,
and they are projective by the Yoneda lemma. When `D` is linear over a ring `R`, so is the
category `D ⥤+ A` of additive functors into any preadditive `A`, with `r ∈ R` acting on
`φ : F ⟶ G` by `φ ≫ G(r • 𝟙)` ([Mitchell, §11]); in particular `ModCat D` is `R`-linear. This
structure is a definition with a scoped instance, not a global instance: at `R = ℤ` it agrees with
the canonical action of the abelian groups `F ⟶ G` only propositionally, and when `A` is
`R`-linear the action through the target is different. Finally, finitely presented functors are
additive, so `mod C` is a full subcategory of `ModCat C`.

## Main definitions

* `TauCeti.ModCat C`: the category `Cᵒᵖ ⥤+ AddCommGrpCat.{w}` of `C`-modules.
* `TauCeti.ModCat.yoneda C : C ⥤ ModCat C`: the Yoneda embedding `X ↦ Hom(-, X)`.
* `TauCeti.AdditiveFunctor.smulEnd R r G : G ⟶ G`: the action of `r ∈ R` on an additive functor
  `G` out of an `R`-linear category.
* `TauCeti.AdditiveFunctor.sourceToCatCenter R : R →+* CatCenter (D ⥤+ A)`: this action as a
  ring homomorphism into the center.
* `TauCeti.AdditiveFunctor.sourceLinear R : Linear R (D ⥤+ A)`: the `R`-linear structure induced
  by an `R`-linear source, for a ring `R`.
* `TauCeti.ModCat.ofFinitelyPresented C`: the fully faithful inclusion `mod C ⥤ ModCat C`.

## Main results

* `TauCeti.additiveFunctor_isClosedUnderLimitsOfShape`,
  `TauCeti.additiveFunctor_isClosedUnderColimitsOfShape`: additive functors are closed under the
  limits and colimits of the target, together with instances for zero, kernels, cokernels and
  all existing finite products.
* `Abelian (ModCat C)` and `HasColimitsOfShape J (ModCat C)`, found by instance inference from
  the closure instances and Mathlib's full-subcategory instances.
* `Projective ((ModCat.yoneda C).obj X)`: representable modules are projective.
* `TauCeti.ModCat.linear`: the scoped instance `Linear R (D ⥤+ AddCommGrpCat)` for an `R`-linear
  preadditive category `D`; after `open scoped TauCeti.ModCat`, specializing `D` to an opposite
  category gives `Linear R (ModCat D)`.
* `TauCeti.AdditiveFunctor.sourceLinear_smul_int`, `TauCeti.AdditiveFunctor.smulEnd_int`,
  `TauCeti.AdditiveFunctor.smulEnd_nat`: at `ℤ` and `ℕ` the source action is the canonical
  multiple.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §§3, 11.
-/

public section

universe w v u

open CategoryTheory Limits Opposite ZeroObject

namespace TauCeti

section Closure

variable {D : Type*} [Category* D] [Preadditive D] {A : Type*} [Category* A] [Preadditive A]

/-- A limit of additive functors is additive when evaluation at each object of `D` preserves
limits of shape `J`: then `F.map (f + g)` is detected by its composites with the projections of
the pointwise limit. -/
theorem additiveFunctor_isClosedUnderLimitsOfShape_of_preserves (J : Type*) [Category* J]
    [∀ Y : D, PreservesLimitsOfShape J ((evaluation D A).obj Y)] :
    (additiveFunctor D A).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro F ⟨h⟩
    refine ⟨fun {X Y f g} ↦ ?_⟩
    refine (isLimitOfPreserves ((evaluation D A).obj Y) h.isLimit).hom_ext fun j ↦ ?_
    have : (h.diag.obj j).Additive := h.prop_diag_obj j
    have hn (u : X ⟶ Y) : F.map u ≫ (h.π.app j).app Y = (h.π.app j).app X ≫ (h.diag.obj j).map u :=
      (h.π.app j).naturality u
    simp only [Functor.mapCone_π_app, evaluation_obj_map, Preadditive.add_comp, hn,
      Functor.map_add, Preadditive.comp_add]

/-- A limit of additive functors is additive: limits in `D ⥤ A` are computed pointwise. -/
instance additiveFunctor_isClosedUnderLimitsOfShape (J : Type*) [Category* J]
    [HasLimitsOfShape J A] : (additiveFunctor D A).IsClosedUnderLimitsOfShape J :=
  additiveFunctor_isClosedUnderLimitsOfShape_of_preserves J

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

/-- A finite product of additive functors is additive, whenever it exists in `D ⥤ A`. A finite
product in the preadditive category `D ⥤ A` is a biproduct, so the additive evaluation functors
preserve it, even when `A` lacks other finite products. -/
instance : (additiveFunctor D A).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape _ _ := additiveFunctor_isClosedUnderLimitsOfShape_of_preserves _

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

namespace AdditiveFunctor

section Semiring

variable (R : Type*) [Semiring R] [Linear R D]

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

/-- The action of an `R`-linear source on additive functors, as a ring homomorphism into the
center of `D ⥤+ A`: the central element attached to `r` has component `smulEnd R r G` at `G`. -/
def sourceToCatCenter : R →+* CatCenter (D ⥤+ A) where
  toFun r := .of { app G := smulEnd R r G, naturality _ _ φ := comp_smulEnd R r φ }
  map_one' := CatCenter.ext _ _ fun G ↦ smulEnd_one R G
  map_mul' r s := CatCenter.ext _ _ fun G ↦ smulEnd_mul R r s G
  map_zero' := CatCenter.ext _ _ fun G ↦ smulEnd_zero R G
  map_add' r s := CatCenter.ext _ _ fun G ↦ smulEnd_add R r s G

/-- The component of `sourceToCatCenter R r` at `G` is `smulEnd R r G`. -/
@[simp]
theorem sourceToCatCenter_app (r : R) (G : D ⥤+ A) :
    (sourceToCatCenter R r).app G = smulEnd R r G := by
  unfold sourceToCatCenter
  rfl

end Semiring

section Ring

variable (R : Type*) [Ring R] [Linear R D]

/-- The `R`-linear structure on `D ⥤+ A` coming from the `R`-linear source `D`: `r ∈ R` acts on
`φ : F ⟶ G` by `φ ≫ smulEnd R r G`, with components `φ_X ≫ G(r • 𝟙 X)` ([Mitchell, §11]). It is
`Linear.ofRingMorphism` applied to `sourceToCatCenter R`.

It is a definition, not an instance, because `D ⥤+ A` may already carry other linear structures.
When `A` is `R`-linear, Mathlib's `functorCategoryLinear` and `Linear.fullSubcategory` give the
pointwise action through the target, which is a different action on functors that are additive
but not `R`-linear. At `R = ℤ`, Mathlib's `preadditiveIntLinear` gives the canonical action of the
abelian groups `F ⟶ G`; it agrees with this one only propositionally (`sourceLinear_smul_int`),
not definitionally. So activating `sourceLinear ℤ` as a local instance creates a non-definitional
diamond; for other rings a local instance is safe as long as `A` is not `R`-linear. For
`D ⥤+ AddCommGrpCat` the scoped instance `TauCeti.ModCat.linear` provides this structure. -/
@[instance_reducible]
def sourceLinear : Linear R (D ⥤+ A) :=
  Linear.ofRingMorphism (sourceToCatCenter R)

section

attribute [local instance] sourceLinear

/-- In `sourceLinear R`, the components of `r • φ` are `φ_X ≫ G(r • 𝟙 X)`. -/
@[simp]
theorem smul_hom_app (r : R) {F G : D ⥤+ A} (φ : F ⟶ G) (X : D) :
    (r • φ).hom.app X = φ.hom.app X ≫ G.obj.map (r • 𝟙 X) := by
  have h : r • φ = φ ≫ (sourceToCatCenter R r).app G := by
    unfold sourceLinear
    exact Linear.smulOfRingMorphism_smul_eq' (sourceToCatCenter R) r φ
  simp [h]

end

end Ring

/-! ### Comparison with the canonical actions of `ℕ` and `ℤ`

Every preadditive category is `ℕ`- and `ℤ`-linear through `preadditiveNatLinear` and
`preadditiveIntLinear`, so `smulEnd` makes sense at `R = ℕ` and `R = ℤ`, and `sourceLinear` at
`R = ℤ` (it needs a ring, so there is no source structure at `ℕ`). They agree there with the
canonical multiples in the abelian groups of morphisms, but only propositionally. -/

/-- At `ℕ`, the action of `n` is the canonical multiple `n • 𝟙 G`. -/
theorem smulEnd_nat [Linear ℕ D] (n : ℕ) (G : D ⥤+ A) : smulEnd ℕ n G = n • 𝟙 G := by
  induction n with
  | zero => simp
  | succ n ih => rw [smulEnd_add, smulEnd_one, ih, succ_nsmul]

/-- At `ℤ`, the action of `n` is the canonical multiple `n • 𝟙 G`: there is only one ring
homomorphism from `ℤ` to the center, so `sourceToCatCenter ℤ` is `Linear.toCatCenter ℤ`. -/
theorem smulEnd_int [Linear ℤ D] (n : ℤ) (G : D ⥤+ A) : smulEnd ℤ n G = n • 𝟙 G := by
  have h : (sourceToCatCenter ℤ n).app G = (Linear.toCatCenter ℤ (D ⥤+ A) n).app G := by
    rw [RingHom.ext_int (sourceToCatCenter ℤ) (Linear.toCatCenter ℤ (D ⥤+ A))]
  rw [sourceToCatCenter_app] at h
  exact h

/-- At `ℤ`, the scalar multiplication of `sourceLinear ℤ` is the canonical `ℤ`-multiple in the
abelian group `F ⟶ G`. The two agree propositionally but not definitionally. -/
theorem sourceLinear_smul_int [Linear ℤ D] (n : ℤ) {F G : D ⥤+ A} (φ : F ⟶ G) :
    ((sourceLinear ℤ).homModule F G).smul n φ = n • φ :=
  int_smul_eq_zsmul ((sourceLinear ℤ).homModule F G) n φ

end AdditiveFunctor

namespace ModCat

/-- **Additive functors into abelian groups out of an `R`-linear category are `R`-linear**, with
the structure `AdditiveFunctor.sourceLinear R`. This is a scoped instance; use
`open scoped TauCeti.ModCat` to get it. It is scoped because at `R = ℤ` it competes with
Mathlib's `preadditiveIntLinear`: the two actions agree only propositionally
(`AdditiveFunctor.sourceLinear_smul_int`), not definitionally. Its low priority makes
`preadditiveIntLinear` win at `ℤ` when the scope is open. -/
scoped instance (priority := low) linear (R : Type*) [Ring R] [Linear R D] :
    Linear R (D ⥤+ AddCommGrpCat.{w}) :=
  AdditiveFunctor.sourceLinear R

end ModCat

open scoped TauCeti.ModCat in
/-- **`Mod D` is `R`-linear** when `D` is, once the scope `TauCeti.ModCat` is open: specialize
the scoped instance `ModCat.linear` to the source `Dᵒᵖ`. -/
example (R : Type*) [Ring R] [Linear R D] : Linear R (ModCat.{w} D) := inferInstance

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
