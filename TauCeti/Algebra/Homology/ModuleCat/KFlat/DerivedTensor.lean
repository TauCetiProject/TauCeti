/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivedTensor
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
public import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.Category.ModuleCat.AB
import Mathlib.RingTheory.Flat.CategoryTheory
public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic

/-!
# Derived tensor products on unbounded module derived categories

Over a commutative ring `R`, the K-flat localizer morphism
`CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)` is a left derivability structure
(`TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure`), so the general construction of
`TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor` provides the left derived tensor product
bifunctor `TauCeti.derivedTensor (ModuleCat.{u} R)` on the unbounded derived category of
`R`-modules, together with its K-flat model comparisons and unitors.

For any left derived bifunctor `(LF, α)` of the tensor product and a bounded-above complex of flat
`R`-modules on either side, the derived tensor product on complex models is naturally isomorphic to
the ordinary totalized tensor product followed by `DerivedCategory.Q`.

## Main definitions

* `TauCeti.leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat`,
  `TauCeti.leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat`: for a bounded-above complex of flat
  `R`-modules in the left or right variable, the natural isomorphism between the derived tensor
  functor on complex models and the ordinary totalized tensor functor followed by `Q`.

## References

* [The Stacks Project][stacks], Section 15.60, Lemma 15.60.12 (Tag 064L) and
  Definition 15.60.13 (Tag 064M).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor Limits HomologicalComplex
open scoped MonoidalCategory

universe u w

namespace TauCeti

section ModelComparison

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (LF : DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
  (α : (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj DerivedCategory.Q).obj
    DerivedCategory.Q).obj LF ⟶
      MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))
  [LF.IsLeftDerivedFunctor₂ α
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]

/-- **Bounded-above flat models compute derived tensor products in the left variable.** If `P` is a
bounded-above complex of flat `R`-modules, then
`DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P)` is naturally isomorphic to the ordinary
totalized tensor functor `P ⊗ -` followed by `DerivedCategory.Q`. -/
def leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Module.Flat R (P.X i)] :
    DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅
      (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj P ⋙
        DerivedCategory.Q := by
  have : P.IsKFlat := P.isKFlat_of_boundedAbove_flat b
  have := isIso_bifunctorCounit₁_of_isKFlat_of_isLeftDerivedFunctor₂_tensor LF α P
  exact asIso (Functor.bifunctorCounit₁ α P)

/-- The forward natural transformation of `leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat` is
`Functor.bifunctorCounit₁ α P`. -/
@[simp]
theorem leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat_hom
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Module.Flat R (P.X i)] :
    (leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat LF α P b).hom =
      Functor.bifunctorCounit₁ α P := by
  have : P.IsKFlat := P.isKFlat_of_boundedAbove_flat b
  simp [leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat]

/-- **Bounded-above flat models compute derived tensor products in the right variable.** If `Q` is
a bounded-above complex of flat `R`-modules, then
`DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q)` is naturally isomorphic to the ordinary
totalized tensor functor `- ⊗ Q` followed by `DerivedCategory.Q`. -/
def leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] [∀ i, Module.Flat R (Q.X i)] :
    DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q) ≅
      (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).flip.obj Q ⋙
        DerivedCategory.Q := by
  have : Q.IsKFlat := Q.isKFlat_of_boundedAbove_flat b
  have := isIso_bifunctorCounit₂_of_isKFlat_of_isLeftDerivedFunctor₂_tensor LF α Q
  exact asIso (Functor.bifunctorCounit₂ α Q)

/-- The forward natural transformation of `leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat` is
`Functor.bifunctorCounit₂ α Q`. -/
@[simp]
theorem leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat_hom
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] [∀ i, Module.Flat R (Q.X i)] :
    (leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat LF α Q b).hom =
      Functor.bifunctorCounit₂ α Q := by
  have : Q.IsKFlat := Q.isKFlat_of_boundedAbove_flat b
  simp [leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat]

end ModelComparison

end TauCeti

/-! ### Further results -/

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace CategoryTheory.Functor

variable {R : Type u} [CommRing R] {H : Type*} [Category* H]
  (F : CochainComplex (ModuleCat.{u} R) ℤ ⥤ H)
  (hF : (quasiIso (ModuleCat.{u} R) (.up ℤ)).IsInvertedBy F)
  {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  {L₁ : CochainComplex (ModuleCat.{u} R) ℤ ⥤ D₁} {L₂ : CochainComplex (ModuleCat.{u} R) ℤ ⥤ D₂}
  [L₁.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))]
  [L₂.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))] {LF : D₁ ⥤ D₂ ⥤ H}
  (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶
    MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (whiskeringRight _ _ _).obj F)
  [LF.IsLeftDerivedFunctor₂ α
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]

include hF in
/-- **Flat-model comparison on the left.** When `F` inverts quasi-isomorphisms, any left derived
bifunctor `(LF, α)` of
`curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible
comparison component `(α.app P).app L` whenever `P` is a bounded-above complex of flat
`R`-modules. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_left
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ n, Module.Flat R (P.X n)) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((α.app P).app L) :=
  have := CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat P b hP
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left F hF α P L

include hF in
/-- **Flat-model comparison on the right.** When `F` inverts quasi-isomorphisms, any left derived
bifunctor `(LF, α)` of
`curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible
comparison component `(α.app K).app Q` whenever `Q` is a bounded-above complex of flat
`R`-modules. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_right
    (K Q : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [Q.IsStrictlyLE b]
    (hQ : ∀ n, Module.Flat R (Q.X n)) : IsIso ((α.app K).app Q) :=
  have := CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat Q b hQ
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right F hF α K Q

end CategoryTheory.Functor
