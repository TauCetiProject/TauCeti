/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-!
# Closure properties and linear structures of additive functors

This file collects closure properties of additive functors inside functor categories, and the
linear structure on additive functors out of a linear category.

A biproduct `⨁ P` of functors `P j : C ⥤ D` into a preadditive category acts on a morphism `a` as
the sum over `j` of the projection to `P j`, the action of `P j` on `a`, and the inclusion of
`P j` (`CategoryTheory.biproduct_functor_map_eq_sum`). So a finite biproduct, and hence a finite
coproduct, of additive functors is additive. A quotient of an additive functor
`C ⥤ AddCommGrpCat` is additive, since every element of its values lifts to the additive functor.

Kernels, cokernels and (co)limits in a functor category are computed pointwise, so a (co)limit
of additive functors is again additive. Hence the additive functors `D ⥤ A` into a preadditive
category `A` contain zero and are closed under kernels, cokernels, and all limits and colimits
that exist in `A`. They are also closed under every finite product that exists in `D ⥤ A`, since
such a product is a biproduct and the additive evaluation functors preserve it.
In particular, additive functors have filtered colimits when the target does, and these colimits
are exact when the target has finite limits and satisfies AB5.

When `D` is linear over a ring `R`, so is the category `D ⥤+ A` of additive functors into any
preadditive `A`, with `r ∈ R` acting on `φ : F ⟶ G` by `φ ≫ G(r • 𝟙)` ([Mitchell, §11]). This
structure is a definition, not an instance: at `R = ℤ` it agrees with the canonical action of the
abelian groups `F ⟶ G` only propositionally, and when `A` is `R`-linear the action through the
target is different.

## Main definitions

* `CategoryTheory.AdditiveFunctor.smulEnd R r G : G ⟶ G`: the action of `r ∈ R` on an additive
  functor `G` out of an `R`-linear category.
* `CategoryTheory.AdditiveFunctor.sourceToCatCenter R : R →+* CatCenter (D ⥤+ A)`: this action as
  a ring homomorphism into the center.
* `CategoryTheory.AdditiveFunctor.sourceLinear R : Linear R (D ⥤+ A)`: the `R`-linear structure
  induced by an `R`-linear source, for a ring `R`.

## Main results

* `CategoryTheory.biproduct_functor_map_eq_sum`: the action of a biproduct of functors on
  morphisms.
* `CategoryTheory.Functor.additive_biproduct`, `CategoryTheory.Functor.additive_sigma`: finite
  biproducts and finite coproducts of additive functors are additive.
* `CategoryTheory.Functor.additive_of_epi`: a quotient of an additive functor
  `C ⥤ AddCommGrpCat` is additive.
* `TauCeti.additiveFunctor_isClosedUnderLimitsOfShape`,
  `TauCeti.additiveFunctor_isClosedUnderColimitsOfShape`: additive functors are closed under the
  limits and colimits of the target, together with instances for zero, kernels, cokernels and
  all existing finite products.
* `CategoryTheory.AdditiveFunctor.sourceLinear_smul_eq_comp_smulEnd`: in `sourceLinear R`, the
  scalar `r` acts on `φ : F ⟶ G` as `φ ≫ smulEnd R r G`.
* `CategoryTheory.AdditiveFunctor.sourceLinear_smul_int`,
  `CategoryTheory.AdditiveFunctor.smulEnd_int`, `CategoryTheory.AdditiveFunctor.smulEnd_nat`: at
  `ℤ` and `ℕ` the source action is the canonical multiple.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §11.
-/

public section

universe v w w'

open CategoryTheory Limits ZeroObject

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] [Preadditive D]

/-- A biproduct `⨁ P` of functors acts on a morphism `a` as the sum, over the summands, of the
projection, the action of the summand on `a`, and the inclusion. -/
theorem biproduct_functor_map_eq_sum {J : Type*} [Fintype J] (P : J → C ⥤ D) [HasBiproduct P]
    {Z W : C} (a : Z ⟶ W) :
    (⨁ P).map a = ∑ j, (biproduct.π P j).app Z ≫ (P j).map a ≫ (biproduct.ι P j).app W := by
  calc (⨁ P).map a = (𝟙 (⨁ P) : ⨁ P ⟶ ⨁ P).app Z ≫ (⨁ P).map a := by simp
    _ = _ := by
      rw [← biproduct.total, NatTrans.app_sum, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [NatTrans.comp_app, Category.assoc, (biproduct.ι P j).naturality]

namespace Functor

variable [Preadditive C]

/-- A finite biproduct of additive functors is additive. -/
instance additive_biproduct {J : Type*} [Finite J] (P : J → C ⥤ D) [HasBiproduct P]
    [∀ j, (P j).Additive] : (⨁ P).Additive where
  map_add {Z W a b} := by
    have := Fintype.ofFinite J
    simp only [biproduct_functor_map_eq_sum, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, Finset.sum_add_distrib]

/-- A finite coproduct of additive functors is additive. -/
instance additive_sigma {J : Type*} [Finite J] (P : J → C ⥤ D) [HasCoproduct P]
    [∀ j, (P j).Additive] : (∐ P).Additive :=
  have := Fintype.ofFinite J
  have := HasBiproduct.of_hasCoproduct P
  additive_of_iso (biproduct.isoCoproduct P)

/-- A quotient of an additive functor `C ⥤ AddCommGrpCat` is additive: every element of a value
of the quotient lifts to the additive functor. -/
theorem additive_of_epi {F G : C ⥤ AddCommGrpCat.{v}} [F.Additive] (q : F ⟶ G) [Epi q] :
    G.Additive where
  map_add {Z W a b} := by
    ext x
    obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (q.app Z)).1 inferInstance x
    simp only [AddCommGrpCat.hom_add_apply, ← NatTrans.naturality_apply, Functor.map_add,
      _root_.map_add]

end Functor

end CategoryTheory

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

/-- Additive functors have filtered colimits of every size supported by the target category. -/
instance [HasFilteredColimitsOfSize.{w, w'} A] : HasFilteredColimitsOfSize.{w, w'} (D ⥤+ A) where
  HasColimitsOfShape _ _ _ := inferInstance

/-- Filtered colimits of additive functors are exact if they are exact in a target with finite
limits. -/
noncomputable instance [HasFiniteLimits A] [HasFilteredColimitsOfSize.{w, w'} A]
    [AB5OfSize.{w, w'} A] : AB5OfSize.{w, w'} (D ⥤+ A) where
  ofShape J _ _ := by
    have : (additiveFunctor D A).IsClosedUnderFiniteLimits := ⟨fun _ _ _ ↦ inferInstance⟩
    exact HasExactColimitsOfShape.domain_of_functor J (additiveFunctor D A).ι

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

end TauCeti

namespace CategoryTheory.AdditiveFunctor

variable {D : Type*} [Category* D] [Preadditive D] {A : Type*} [Category* A] [Preadditive A]

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

/-- In `sourceLinear R`, the scalar `r` acts on `φ : F ⟶ G` by composing with the action
`smulEnd R r G` on the target. -/
theorem sourceLinear_smul_eq_comp_smulEnd (r : R) {F G : D ⥤+ A} (φ : F ⟶ G) :
    r • φ = φ ≫ smulEnd R r G := by
  rw [← sourceToCatCenter_app]
  exact Linear.smulOfRingMorphism_smul_eq' (sourceToCatCenter R) r φ

/-- In `sourceLinear R`, the components of `r • φ` are `φ_X ≫ G(r • 𝟙 X)`. -/
@[simp]
theorem sourceLinear_smul_hom_app (r : R) {F G : D ⥤+ A} (φ : F ⟶ G) (X : D) :
    (r • φ).hom.app X = φ.hom.app X ≫ G.obj.map (r • 𝟙 X) := by
  simp [sourceLinear_smul_eq_comp_smulEnd]

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

end CategoryTheory.AdditiveFunctor
