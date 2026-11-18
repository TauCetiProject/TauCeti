/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
import TauCeti.Algebra.Homology.Monoidal.KFlat.Tensor

/-!
# Derived tensor products from K-flat complexes

Tensoring with a fixed K-flat complex preserves quasi-isomorphisms, hence descends to an
endofunctor of the unbounded derived category (`CochainComplex.kFlatTensor`).
`CochainComplex.kFlatTensorModelIso` identifies its value on a complex with the usual direct-sum
total tensor product, and maps between K-flat complexes induce natural transformations
(`CochainComplex.kFlatTensorMap`) with identity and composition laws and a formula on complex
models.

When `C` is braided, `CochainComplex C ℤ` carries Mathlib's totalized monoidal structure, and
`CochainComplex.kFlatLocalizerMorphism C` is a left derivability structure (for example when
`C = ModuleCat.{u} R`, via `TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure`),
taking the external product of `CochainComplex.kFlatLocalizerMorphism C` with itself shows that
totalized tensoring followed by localization to `DerivedCategory C` admits a left derived bifunctor
(`TauCeti.hasLeftDerivedFunctor₂_tensor`). This yields a canonical choice `TauCeti.derivedTensor C`,
while all model-comparison and unit properties hold universally for any left derived bifunctor
`(LT, α)` of tensoring:

* When `K` is K-flat (for instance when `K` is bounded above with flat terms,
  `CochainComplex.isKFlat_of_boundedAbove_flat`), `(α.app K).app L` is an isomorphism for every
  unbounded complex `L`, so `Functor.bifunctorCounit₁ α K` is a natural isomorphism and
  `LT.obj (DerivedCategory.Q.obj K)` is naturally isomorphic to `K.kFlatTensor`
  (`TauCeti.derivedTensorObjIsoKFlatTensor`), compatibly with `CochainComplex.kFlatTensorMap`
  (`TauCeti.derivedTensorObjIsoKFlatTensor_hom_naturality`).
* Symmetrically, when `L` is K-flat (for instance when `L` is bounded above with flat terms),
  `(α.app K).app L` is an isomorphism for every unbounded complex `K`, so
  `Functor.bifunctorCounit₂ α L` is a natural isomorphism.
* Tensoring on the left or right with the monoidal unit complex `𝟙_ (CochainComplex C ℤ)` is
  naturally isomorphic to the identity endofunctor of `DerivedCategory C`
  (`TauCeti.derivedTensorLeftUnitor`, `TauCeti.derivedTensorRightUnitor`).

## Main definitions

* `CochainComplex.kFlatTensor`, `CochainComplex.kFlatTensorModelIso`,
  `CochainComplex.kFlatTensorMap`: derived tensoring with a fixed K-flat complex on the left.
* `TauCeti.derivedTensor`: a left derived bifunctor on `DerivedCategory C`, with counit
  `TauCeti.derivedTensorCounit`.
* `TauCeti.derivedTensorObjIsoKFlatTensor`: comparison `LT.obj (Q.obj K) ≅ K.kFlatTensor` for any
  K-flat complex `K` and any left derived tensor bifunctor `(LT, α)`.
* `TauCeti.derivedTensorLeftUnitor`, `TauCeti.derivedTensorRightUnitor`: left and right unit
  natural isomorphisms on `DerivedCategory C`.

## Main results

* `TauCeti.hasLeftDerivedFunctor₂_tensor`: the unbounded tensor product of cochain complexes admits
  a left derived bifunctor whenever `CochainComplex.kFlatLocalizerMorphism C` is a left
  derivability structure.
* `TauCeti.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left` and
  `TauCeti.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right`: one-sided K-flat
  complexes compute the derived tensor product against arbitrary unbounded complexes.
* `TauCeti.isIso_bifunctorCounit₁_tensor_of_boundedAbove_flat` and
  `TauCeti.isIso_bifunctorCounit₂_tensor_of_boundedAbove_flat`: bounded-above flat complexes
  compute the derived tensor product on either side.
* `TauCeti.derivedTensorObjIsoKFlatTensor_hom_naturality`: naturality of
  `TauCeti.derivedTensorObjIsoKFlatTensor` with respect to `CochainComplex.kFlatTensorMap`.

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 06Y0, 06Y4, 064L, and 064M.
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
* [Joël Riou, *Formalization of derived categories in {Lean}/mathlib*][riou-2025]

The descent and derived-bifunctor constructions use Mathlib's `Localization.lift`,
`Localization.liftNatTrans`, `Functor.HasLeftDerivedFunctor₂`, and `LocalizerMorphism.prod`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.MonoidalCategory
  HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasDerivedCategory C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- Tensoring with a K-flat complex, followed by localization, inverts quasi-isomorphisms. -/
theorem isInvertedBy_tensor_comp_Q (K : CochainComplex C ℤ) [K.IsKFlat] :
    (quasiIso C (.up ℤ)).IsInvertedBy
      (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q) := by
  intro A B f hf
  have : QuasiIso f := hf
  simpa only [Functor.comp_map, Functor.comp_obj, curriedTensor_map₂CochainComplex_obj_obj,
    curriedTensor_map₂CochainComplex_obj_map] using
    (inferInstance : IsIso (DerivedCategory.Q.map (tensorHom (𝟙 K) f)))

/-- Tensoring a derived object with the specified K-flat complex on the left. -/
def kFlatTensor (K : CochainComplex C ℤ) [K.IsKFlat] :
    DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift
    (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
      DerivedCategory.Q)
    K.isInvertedBy_tensor_comp_Q DerivedCategory.Q

/-- The derived tensor functor is the localization lift of the ordinary total tensor. -/
theorem kFlatTensor_eq_lift (K : CochainComplex C ℤ) [K.IsKFlat] :
    K.kFlatTensor = Localization.lift
      (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q) K.isInvertedBy_tensor_comp_Q DerivedCategory.Q := (rfl)

instance (K : CochainComplex C ℤ) [K.IsKFlat] :
    Localization.Lifting DerivedCategory.Q (quasiIso C (.up ℤ))
      (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q) K.kFlatTensor := by
  rw [kFlatTensor_eq_lift]
  infer_instance

/-- The tensor with a K-flat complex is computed by the ordinary total tensor on complex models.
This comparison is natural in the right factor. -/
def kFlatTensorModelIso (K : CochainComplex C ℤ) [K.IsKFlat] :
    DerivedCategory.Q ⋙ K.kFlatTensor ≅
      ((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q :=
  Localization.Lifting.iso _ (quasiIso C (.up ℤ)) _ _

/-- The model comparison is the canonical factorization isomorphism of the localization. -/
theorem kFlatTensorModelIso_eq_liftingIso (K : CochainComplex C ℤ) [K.IsKFlat] :
    K.kFlatTensorModelIso = Localization.Lifting.iso DerivedCategory.Q (quasiIso C (.up ℤ))
      (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q) K.kFlatTensor := (rfl)

/-- A map between K-flat complexes induces a transformation of their derived tensor functors. -/
def kFlatTensorMap {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat] (f : K ⟶ L) :
    K.kFlatTensor ⟶ L.kFlatTensor :=
  Localization.liftNatTrans DerivedCategory.Q (quasiIso C (.up ℤ)) _ _ _ _
    (whiskerRight ((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.map f)
      DerivedCategory.Q)

/-- The induced transformation is the localization lift of the ordinary tensor transformation. -/
theorem kFlatTensorMap_eq_liftNatTrans {K L : CochainComplex C ℤ}
    [K.IsKFlat] [L.IsKFlat] (f : K ⟶ L) :
    kFlatTensorMap f = Localization.liftNatTrans DerivedCategory.Q (quasiIso C (.up ℤ))
      _ _ K.kFlatTensor L.kFlatTensor
      (whiskerRight ((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.map f)
        DerivedCategory.Q) := by
  rfl

/-- On a complex model, the transformation is the image of tensoring the given map with the
identity, conjugated by the model comparisons. -/
theorem kFlatTensorMap_app_Q {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) (A : CochainComplex C ℤ) :
    (kFlatTensorMap f).app (DerivedCategory.Q.obj A) =
      (K.kFlatTensorModelIso.app A).hom ≫ DerivedCategory.Q.map (tensorHom f (𝟙 A)) ≫
        (L.kFlatTensorModelIso.app A).inv := by
  simp only [kFlatTensorMap, Localization.liftNatTrans_app, whiskerRight_app,
    curriedTensor_map₂CochainComplex_map_app, kFlatTensorModelIso, Iso.app_hom, Iso.app_inv,
    Functor.comp_obj, curriedTensor_map₂CochainComplex_obj_obj]

/-- The model comparison intertwines the induced transformation with the ordinary tensor map. -/
@[reassoc (attr := simp)]
theorem kFlatTensorMap_app_Q_comp {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) (A : CochainComplex C ℤ) :
    (kFlatTensorMap f).app (DerivedCategory.Q.obj A) ≫ L.kFlatTensorModelIso.hom.app A =
      K.kFlatTensorModelIso.hom.app A ≫ DerivedCategory.Q.map (tensorHom f (𝟙 A)) := by
  rw [← Iso.app_hom K.kFlatTensorModelIso A, ← Iso.app_hom L.kFlatTensorModelIso A,
    kFlatTensorMap_app_Q]
  simp only [Category.assoc, ← curriedTensor_map₂CochainComplex_obj_obj L A,
    Iso.inv_hom_id, Category.comp_id]

@[simp]
theorem kFlatTensorMap_id (K : CochainComplex C ℤ) [K.IsKFlat] :
    kFlatTensorMap (𝟙 K) = 𝟙 K.kFlatTensor := by
  simp [kFlatTensorMap]

@[simp]
theorem kFlatTensorMap_comp {K L M : CochainComplex C ℤ}
    [K.IsKFlat] [L.IsKFlat] [M.IsKFlat] (f : K ⟶ L) (g : L ⟶ M) :
    kFlatTensorMap (f ≫ g) = kFlatTensorMap f ≫ kFlatTensorMap g := by
  simp only [kFlatTensorMap, Functor.map_comp, whiskerRight_comp]
  exact (Localization.comp_liftNatTrans DerivedCategory.Q (quasiIso C (.up ℤ))
    _ _ _ _ _ _ _ _).symm

end CochainComplex

namespace TauCeti

open CochainComplex

universe w

section DerivedTensor

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasDerivedCategory.{w} C]

variable (C) in
/-- Totalized tensor product on `CochainComplex C ℤ` followed by localization to
`DerivedCategory C` in the second variable. -/
abbrev tensorCompQ :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ DerivedCategory C :=
  MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
    (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C))

variable [BraidedCategory C]

variable (C) in
/-- The product K-flat localizer morphism derives the uncurried total tensor product of cochain
complexes. -/
theorem derives_uncurry_tensorCompQ :
    ((kFlatLocalizerMorphism C).prod (kFlatLocalizerMorphism C)).Derives
      (Functor.uncurry.obj (tensorCompQ C)) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁.hom := by simpa [mem_quasiIso_iff] using hf₁
  have : QuasiIso f₂.hom := by simpa [mem_quasiIso_iff] using hf₂
  have hmap : (((kFlatLocalizerMorphism C).prod (kFlatLocalizerMorphism C)).functor ⋙
        Functor.uncurry.obj (tensorCompQ C)).map (f₁, f₂) =
      DerivedCategory.Q.map (HomologicalComplex.tensorHom f₁.hom f₂.hom) := by
    dsimp [tensorCompQ, kFlatLocalizerMorphism]
    rw [← Functor.map_comp, whiskerRight_eq_mapBifunctorMap, whiskerLeft_eq_mapBifunctorMap,
      ← mapBifunctorMap_comp, Category.comp_id, Category.id_comp]
  have := quasiIso_tensorHom_of_isKFlat_right_left f₁.hom f₂.hom
  rw [hmap]
  infer_instance

variable [(kFlatLocalizerMorphism C).IsLeftDerivabilityStructure]

variable (C) in
/-- **Existence of the derived tensor product.** When `CochainComplex.kFlatLocalizerMorphism C` is
a left derivability structure, the totalized tensor product on `CochainComplex C ℤ` followed by
localization to `DerivedCategory C` admits a left derived bifunctor with respect to
quasi-isomorphisms in both variables. -/
instance hasLeftDerivedFunctor₂_tensor :
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := C))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  have := (derives_uncurry_tensorCompQ C).hasPointwiseLeftDerivedFunctor
  exact Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

section ModelComparison

variable {LT : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C}
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj LT ⟶
    tensorCompQ C)
  [LT.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]

/-- On a pair of K-flat complexes, the counit of any left derived tensor bifunctor is an
isomorphism. -/
private lemma isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat
    (K L : CochainComplex C ℤ) [K.IsKFlat] [L.IsKFlat] :
    IsIso ((α.app K).app L) :=
  (derives_uncurry_tensorCompQ C).isIso' (Functor.whiskeringLeft₂HomEquiv α)
    (⟨K, ‹_›⟩, ⟨L, ‹_›⟩)

/-- **Left K-flat model comparison.** When `K` is K-flat, `(α.app K).app L` is an isomorphism for
every (possibly unbounded and non-K-flat) cochain complex `L` in `C`. -/
instance isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left
    (K L : CochainComplex C ℤ) [K.IsKFlat] :
    IsIso ((α.app K).app L) := by
  obtain ⟨R⟩ : Nonempty ((kFlatLocalizerMorphism C).LeftResolution L) := inferInstance
  let P : CochainComplex C ℤ := R.X₁.obj
  let π : P ⟶ L := R.w
  have : QuasiIso π := (mem_quasiIso_iff π).1 R.hw
  have := isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat α K P
  have hnat := (α.app K).naturality π
  dsimp [tensorCompQ] at hnat
  have : IsIso (DerivedCategory.Q.map (K ◁ π)) := by
    rw [whiskerLeft_eq_mapBifunctorMap]
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (HomologicalComplex.tensorHom (𝟙 K) π)))
  rw [← isIso_comp_left_iff ((LT.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map π)),
    hnat]
  infer_instance

/-- When `K` is K-flat, `Functor.bifunctorCounit₁ α K` is a natural isomorphism. -/
instance isIso_bifunctorCounit₁_tensor_of_isKFlat
    (K : CochainComplex C ℤ) [K.IsKFlat] :
    IsIso (Functor.bifunctorCounit₁ α K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro L
  dsimp only [Functor.bifunctorCounit₁_app]
  infer_instance

/-- **Right K-flat model comparison.** When `L` is K-flat, `(α.app K).app L` is an isomorphism for
every (possibly unbounded and non-K-flat) cochain complex `K` in `C`. -/
instance isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right
    (K L : CochainComplex C ℤ) [L.IsKFlat] :
    IsIso ((α.app K).app L) := by
  obtain ⟨R⟩ : Nonempty ((kFlatLocalizerMorphism C).LeftResolution K) := inferInstance
  let P : CochainComplex C ℤ := R.X₁.obj
  let π : P ⟶ K := R.w
  have : QuasiIso π := (mem_quasiIso_iff π).1 R.hw
  have := isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat α P L
  have hnat := NatTrans.congr_app (α.naturality π) L
  dsimp [tensorCompQ] at hnat
  have : IsIso (DerivedCategory.Q.map (π ▷ L)) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (HomologicalComplex.tensorHom π (𝟙 L))))
  rw [← isIso_comp_left_iff (((LT.map (DerivedCategory.Q.map π)).app (DerivedCategory.Q.obj L))),
    hnat]
  infer_instance

/-- When `L` is K-flat, `Functor.bifunctorCounit₂ α L` is a natural isomorphism. -/
instance isIso_bifunctorCounit₂_tensor_of_isKFlat
    (L : CochainComplex C ℤ) [L.IsKFlat] :
    IsIso (Functor.bifunctorCounit₂ α L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  dsimp only [Functor.bifunctorCounit₂_app]
  infer_instance

include α in
/-- When `K` is bounded above with flat terms and sequential colimits in `C` are exact and commute
with tensoring, `Functor.bifunctorCounit₁ α K` is a natural isomorphism. -/
theorem isIso_bifunctorCounit₁_tensor_of_boundedAbove_flat
    [∀ M : C, PreservesFiniteColimits (tensorLeft M)]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    (K : CochainComplex C ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (tensorLeft (K.X i))] :
    IsIso (Functor.bifunctorCounit₁ α K) :=
  have := K.isKFlat_of_boundedAbove_flat b
  inferInstance

include α in
/-- When `L` is bounded above with flat terms and sequential colimits in `C` are exact and commute
with tensoring, `Functor.bifunctorCounit₂ α L` is a natural isomorphism. -/
theorem isIso_bifunctorCounit₂_tensor_of_boundedAbove_flat
    [∀ M : C, PreservesFiniteColimits (tensorLeft M)]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    (L : CochainComplex C ℤ) (b : ℤ)
    [L.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (tensorLeft (L.X i))] :
    IsIso (Functor.bifunctorCounit₂ α L) :=
  have := L.isKFlat_of_boundedAbove_flat b
  inferInstance

end ModelComparison

variable (C) in
/-- The canonical left derived tensor bifunctor on the unbounded derived category
`DerivedCategory C`. -/
def derivedTensor :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C :=
  Functor.leftDerived₂ (tensorCompQ C) DerivedCategory.Q DerivedCategory.Q
    (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))

variable (C) in
/-- The universal counit natural transformation exhibiting `TauCeti.derivedTensor C` as a left
derived bifunctor of totalized tensoring of cochain complexes. -/
def derivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj
      (derivedTensor C) ⟶ tensorCompQ C :=
  Functor.leftDerivedCounit₂ (tensorCompQ C) DerivedCategory.Q DerivedCategory.Q
    (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))

variable (C) in
instance isLeftDerivedFunctor₂_derivedTensor :
    (derivedTensor C).IsLeftDerivedFunctor₂ (derivedTensorCounit C)
      (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) := by
  dsimp [derivedTensor, derivedTensorCounit]
  infer_instance

section UniversalProperties

variable {LT : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C}
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj LT ⟶
    tensorCompQ C)
  [LT.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]

include α

/-- For any K-flat complex `K` and any left derived tensor bifunctor `(LT, α)`, evaluating `LT` at
`DerivedCategory.Q.obj K` is naturally isomorphic to `K.kFlatTensor`. -/
def derivedTensorObjIsoKFlatTensor (K : CochainComplex C ℤ) [K.IsKFlat] :
    LT.obj (DerivedCategory.Q.obj K) ≅ K.kFlatTensor :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ LT.obj (DerivedCategory.Q.obj K))
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙ DerivedCategory.Q)
    (LT.obj (DerivedCategory.Q.obj K)) K.kFlatTensor
    (asIso (Functor.bifunctorCounit₁ α K) ≪≫
      Functor.isoWhiskerRight ((curriedTensorIsoMap₂CochainComplex C).app K) DerivedCategory.Q)

/-- On complex models, `derivedTensorObjIsoKFlatTensor` intertwines `kFlatTensorModelIso` with the
counit `α` of the left derived tensor bifunctor. -/
@[reassoc (attr := simp)]
lemma derivedTensorObjIsoKFlatTensor_hom_app_Q_comp
    (K L : CochainComplex C ℤ) [K.IsKFlat] :
    (derivedTensorObjIsoKFlatTensor α K).hom.app (DerivedCategory.Q.obj L) ≫
      K.kFlatTensorModelIso.hom.app L = (α.app K).app L := by
  suffices ((α.app K).app L ≫
      (DerivedCategory.Q.map (𝟙 (K ⊗ L)) :
        DerivedCategory.Q.obj (K ⊗ L) ⟶
          DerivedCategory.Q.obj (((curriedTensor C).map₂CochainComplex.obj K).obj L)) :
        (LT.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
          DerivedCategory.Q.obj (((curriedTensor C).map₂CochainComplex.obj K).obj L)) =
      (α.app K).app L by
    simpa [derivedTensorObjIsoKFlatTensor, kFlatTensorModelIso_eq_liftingIso, tensorCompQ,
      -curriedTensor_map₂CochainComplex_obj_obj]
  exact (whisker_eq _ (DerivedCategory.Q.map_id (K ⊗ L))).trans (Category.comp_id _)

/-- The comparison `derivedTensorObjIsoKFlatTensor` is natural with respect to morphisms of K-flat
complexes and `CochainComplex.kFlatTensorMap`. -/
@[reassoc]
lemma derivedTensorObjIsoKFlatTensor_hom_naturality
    {K₁ K₂ : CochainComplex C ℤ} [K₁.IsKFlat] [K₂.IsKFlat] (f : K₁ ⟶ K₂) :
    LT.map (DerivedCategory.Q.map f) ≫ (derivedTensorObjIsoKFlatTensor α K₂).hom =
      (derivedTensorObjIsoKFlatTensor α K₁).hom ≫ kFlatTensorMap f := by
  refine Localization.natTrans_ext DerivedCategory.Q (quasiIso C (.up ℤ)) fun L ↦ ?_
  rw [← cancel_mono (K₂.kFlatTensorModelIso.hom.app L)]
  simp only [NatTrans.comp_app, Category.assoc, derivedTensorObjIsoKFlatTensor_hom_app_Q_comp,
    kFlatTensorMap_app_Q_comp]
  refine (NatTrans.congr_app (α.naturality f) L).trans ?_
  refine (congrArg (fun m ↦ (α.app K₁).app L ≫ DerivedCategory.Q.map m)
    (whiskerRight_eq_mapBifunctorMap f L)).trans ?_
  exact (derivedTensorObjIsoKFlatTensor_hom_app_Q_comp_assoc α K₁ L
    (DerivedCategory.Q.map (HomologicalComplex.tensorHom f (𝟙 L)))).symm

/-- Left unit natural isomorphism `𝟙_[0] ⊗^L M ≅ M` for any left derived tensor bifunctor `(LT, α)`
on `DerivedCategory C`. -/
def derivedTensorLeftUnitor :
    LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≅
      𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C))
    (LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))))
    (𝟭 (DerivedCategory C))
    (asIso (Functor.bifunctorCounit₁ α (𝟙_ (CochainComplex C ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `derivedTensorLeftUnitor` is the derived-tensor counit followed by the
monoidal left unitor of `CochainComplex C ℤ`. -/
@[simp]
lemma derivedTensorLeftUnitor_hom_app_Q (L : CochainComplex C ℤ) :
    (derivedTensorLeftUnitor α).hom.app (DerivedCategory.Q.obj L) =
      (α.app (𝟙_ (CochainComplex C ℤ))).app L ≫ DerivedCategory.Q.map (λ_ L).hom := by
  simp [derivedTensorLeftUnitor]

/-- Right unit natural isomorphism `M ⊗^L 𝟙_[0] ≅ M` for any left derived tensor bifunctor `(LT, α)`
on `DerivedCategory C`. -/
def derivedTensorRightUnitor :
    LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≅
      𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C))
    (LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))))
    (𝟭 (DerivedCategory C))
    (asIso (Functor.bifunctorCounit₂ α (𝟙_ (CochainComplex C ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.rightUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `derivedTensorRightUnitor` is the derived-tensor counit followed by the
monoidal right unitor of `CochainComplex C ℤ`. -/
@[simp]
lemma derivedTensorRightUnitor_hom_app_Q (K : CochainComplex C ℤ) :
    (derivedTensorRightUnitor α).hom.app (DerivedCategory.Q.obj K) =
      (α.app K).app (𝟙_ (CochainComplex C ℤ)) ≫ DerivedCategory.Q.map (ρ_ K).hom := by
  simp [derivedTensorRightUnitor]

end UniversalProperties

end DerivedTensor

end TauCeti
