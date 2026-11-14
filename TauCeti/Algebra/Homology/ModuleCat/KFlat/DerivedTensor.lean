/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure

/-!
# The derived tensor product on unbounded module derived categories

Let `R` be a commutative ring. Combining `TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic` and
`TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure` with the braided monoidal left
derived tensor theory of `TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor`
(`CategoryTheory.LocalizerMorphism.prod` and `CategoryTheory.Functor.HasLeftDerivedFunctor₂`), we
prove that the total tensor product of cochain complexes of `R`-modules admits a left derived
bifunctor `⊗^L` with respect to quasi-isomorphisms (`TauCeti.hasLeftDerivedFunctor₂_tensor`).
Moreover:
* any left derived bifunctor of `curriedTensor ⋙ (whiskeringRight _ _ _).obj F` (for `F` inverting
  quasi-isomorphisms) is computed on the nose when either factor is a bounded-above complex of flat
  `R`-modules (`TauCeti.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_left`
  and `TauCeti.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_right`) or a flat
  `R`-module in a single degree
  (`TauCeti.isIso_app_single_obj_app_of_isLeftDerivedFunctor₂_tensor_of_flat` and
  `TauCeti.isIso_app_app_single_obj_of_isLeftDerivedFunctor₂_tensor_of_flat`);
* `TauCeti.derivedTensor R` provides a canonical choice of `⊗^L` on `DerivedCategory (ModuleCat R)`,
  equipped with one-variable `IsLeftDerivedFunctor` instances via `Functor.bifunctorCounit₁` and
  `Functor.bifunctorCounit₂` and K-flat object isomorphisms `TauCeti.derivedTensorKFlatLeftIso` and
  `TauCeti.derivedTensorKFlatRightIso`.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* J. Riou, *Formalization of derived categories in Lean/mathlib*, Ann. Formaliz. Math. 1 (2025),
  1–42, §5.3.4.
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4),
  [Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L), and
  [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor HomologicalComplex
open scoped MonoidalCategory

universe u w

namespace TauCeti

section FlatComparison

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

include hF in
/-- **Flat-model comparison on the left.** When `F` inverts quasi-isomorphisms, any left derived
bifunctor `(LF, α)` of
`curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible
comparison component `(α.app P).app L` whenever `P` is a bounded-above complex of flat
`R`-modules. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_left
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
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
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (K Q : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [Q.IsStrictlyLE b]
    (hQ : ∀ n, Module.Flat R (Q.X n)) : IsIso ((α.app K).app Q) :=
  have := CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat Q b hQ
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right F hF α K Q

include hF in
/-- When `F` inverts quasi-isomorphisms, any left derived bifunctor `(LF, α)` of
`curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible
comparison component when the left factor is a flat `R`-module placed in a single degree `n`. -/
theorem isIso_app_single_obj_app_of_isLeftDerivedFunctor₂_tensor_of_flat
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (M : ModuleCat.{u} R) [Module.Flat R M] (n : ℤ) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((α.app ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) n).obj M)).app L) :=
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left F hF α _ L

include hF in
/-- When `F` inverts quasi-isomorphisms, any left derived bifunctor `(LF, α)` of
`curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible
comparison component when the right factor is a flat `R`-module placed in a single degree `n`. -/
theorem isIso_app_app_single_obj_of_isLeftDerivedFunctor₂_tensor_of_flat
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) [Module.Flat R M] (n : ℤ) :
    IsIso ((α.app K).app ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) n).obj M)) :=
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right F hF α K _

end FlatComparison

section DerivedCategory

/-- **Existence of the derived tensor product.** For a commutative ring `R`, the total tensor
product of cochain complexes of `R`-modules followed by localization to
`DerivedCategory (ModuleCat R)` admits a left derived bifunctor `⊗^L` with respect to
quasi-isomorphisms in both variables. -/
theorem hasLeftDerivedFunctor₂_tensor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := ModuleCat.{u} R))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor₂_tensor_of_inverts (DerivedCategory.Q (C := ModuleCat.{u} R))
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)))

attribute [instance] hasLeftDerivedFunctor₂_tensor

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The canonical left derived tensor bifunctor `⊗^L` on the unbounded derived category of
`R`-modules. -/
def derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Functor.leftDerived₂
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))
    DerivedCategory.Q DerivedCategory.Q
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))

/-- The universal counit comparing `derivedTensor R` on localized complexes with the ordinary
total tensor product of cochain complexes. -/
def derivedTensorCounit :
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (derivedTensor R) ⟶
      MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
  Functor.leftDerivedCounit₂
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))
    DerivedCategory.Q DerivedCategory.Q
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))

instance : (derivedTensor R).IsLeftDerivedFunctor₂ (derivedTensorCounit R)
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  dsimp [derivedTensor, derivedTensorCounit]; infer_instance

variable {R}

instance (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((derivedTensor R).obj (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor
      (Functor.bifunctorCounit₁ (derivedTensorCounit R) K) (quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
  isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor DerivedCategory.Q
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (derivedTensorCounit R) K

instance (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((derivedTensor R).flip.obj (DerivedCategory.Q.obj L)).IsLeftDerivedFunctor
      (Functor.bifunctorCounit₂ (derivedTensorCounit R) L) (quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
  isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor DerivedCategory.Q
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (derivedTensorCounit R) L

instance (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso (((derivedTensorCounit R).app P).app L) :=
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left DerivedCategory.Q
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (derivedTensorCounit R) P L

instance (K P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso (((derivedTensorCounit R).app K).app P) :=
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right DerivedCategory.Q
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (derivedTensorCounit R) K P

/-- The object isomorphism `((derivedTensor R).obj (DerivedCategory.Q.obj P)).obj
(DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj (P ⊗ L)` induced by `derivedTensorCounit R` when
the left complex `P` is K-flat. -/
def derivedTensorKFlatLeftIso (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    ((derivedTensor R).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (P ⊗ L) :=
  asIso (((derivedTensorCounit R).app P).app L)

/-- The forward morphism of `derivedTensorKFlatLeftIso` is the counit component. -/
@[simp]
lemma derivedTensorKFlatLeftIso_hom (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedTensorKFlatLeftIso P L).hom = ((derivedTensorCounit R).app P).app L := (rfl)

/-- The inverse morphism of `derivedTensorKFlatLeftIso` is the inverse of the counit component. -/
@[simp]
lemma derivedTensorKFlatLeftIso_inv (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedTensorKFlatLeftIso P L).inv = inv (((derivedTensorCounit R).app P).app L) := (rfl)

/-- The object isomorphism `((derivedTensor R).obj (DerivedCategory.Q.obj K)).obj
(DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj (K ⊗ P)` induced by `derivedTensorCounit R` when
the right complex `P` is K-flat. -/
def derivedTensorKFlatRightIso (K P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    ((derivedTensor R).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (K ⊗ P) :=
  asIso (((derivedTensorCounit R).app K).app P)

/-- The forward morphism of `derivedTensorKFlatRightIso` is the counit component. -/
@[simp]
lemma derivedTensorKFlatRightIso_hom (K P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedTensorKFlatRightIso K P).hom = ((derivedTensorCounit R).app K).app P := (rfl)

/-- The inverse morphism of `derivedTensorKFlatRightIso` is the inverse of the counit component. -/
@[simp]
lemma derivedTensorKFlatRightIso_inv (K P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedTensorKFlatRightIso K P).inv = inv (((derivedTensorCounit R).app K).app P) := (rfl)

end DerivedCategory

end TauCeti
