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
# Tensoring derived objects with a K-flat complex

Tensoring with a fixed K-flat complex preserves quasi-isomorphisms, hence descends to an
endofunctor of the unbounded derived category. `CochainComplex.kFlatTensor` is this functor;
`CochainComplex.kFlatTensorModelIso` identifies its value on a complex with the usual
direct-sum total tensor product. Maps between K-flat complexes induce natural transformations,
with identity and composition laws and a formula on complex models.

Only the fixed left factor is required to be K-flat. No boundedness or termwise flatness
is required of the right factor. This is the model computation used to construct derived
tensor products, not a choice of a K-flat replacement for every derived object.

When `C` is braided, `CochainComplex C ℤ` carries its totalized monoidal structure, and the
inclusion of K-flat complexes `CochainComplex.KFlat.localizerMorphism C` is a left derivability
structure (for instance for `C = ModuleCat R` over a commutative ring `R`, see
`TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure`), its external product with
itself derives the totalized tensor product bifunctor followed by `DerivedCategory.Q`, because
tensoring with a K-flat complex on either side preserves quasi-isomorphisms. Consequently the
tensor product admits a left derived bifunctor (`TauCeti.hasLeftDerivedFunctor₂_tensor`,
`TauCeti.derivedTensor`) on the unbounded derived category `DerivedCategory C`.

For any left derived bifunctor `(LF, α)` of the tensor product:
* the partial evaluations `LF.obj (DerivedCategory.Q.obj K)` and
  `LF.flip.obj (DerivedCategory.Q.obj L)` are left derived functors of `K ⊗ -` and `- ⊗ L` via
  `Functor.bifunctorCounit₁ α K` and `Functor.bifunctorCounit₂ α L` for every complex `K` and `L`;
* the comparison `(α.app P).app L` is an isomorphism whenever either `P` or `L` is K-flat, without
  any K-flatness or boundedness assumption on the other factor, in particular whenever either
  factor is a bounded-above complex of flat objects;
* for K-flat `P`, `LF.obj (DerivedCategory.Q.obj P)` is naturally isomorphic to `P.kFlatTensor`
  compatibly with morphisms of K-flat models;
* left and right derived tensoring with the monoidal unit complex `𝟙_ (CochainComplex C ℤ)` is
  naturally isomorphic to the identity of `DerivedCategory C`.

## Main definitions

* `CochainComplex.kFlatTensor`, `CochainComplex.kFlatTensorModelIso`,
  `CochainComplex.kFlatTensorMap`: derived tensoring with a fixed K-flat complex on the left.
* `TauCeti.derivedTensor`, `TauCeti.derivedTensorCounit`: the left derived tensor bifunctor
  `D(C) ⥤ D(C) ⥤ D(C)` and its comparison natural transformation.
* `TauCeti.leftDerivedTensorObjIsoKFlatTensor`: for K-flat `P`, the natural isomorphism identifying
  `LF.obj (DerivedCategory.Q.obj P)` with `P.kFlatTensor`.
* `TauCeti.leftDerivedTensorLeftUnitor`, `TauCeti.leftDerivedTensorRightUnitor`: the left and right
  unit natural isomorphisms of any left derived tensor bifunctor.

## Main results

* `TauCeti.hasLeftDerivedFunctor₂_tensor`: the totalized tensor product of complexes followed by
  `DerivedCategory.Q` has a left derived bifunctor.
* `TauCeti.isIso_app_app_of_isKFlat_left_of_isLeftDerivedFunctor₂_tensor`,
  `TauCeti.isIso_app_app_of_isKFlat_right_of_isLeftDerivedFunctor₂_tensor`: the derived tensor
  comparison `(α.app P).app L` is an isomorphism whenever either `P` or `L` is K-flat.
* `TauCeti.isIso_bifunctorCounit₁_of_boundedAbove_flat_of_isLeftDerivedFunctor₂_tensor`,
  `TauCeti.isIso_bifunctorCounit₂_of_boundedAbove_flat_of_isLeftDerivedFunctor₂_tensor`:
  bounded-above complexes of flat objects compute the derived tensor product on either side.
* `TauCeti.leftDerivedTensorObjIsoKFlatTensor_naturality`: compatibility of the K-flat model
  identification with morphisms between K-flat complexes.

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 064L and 064M.
* Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008),
  1286–1318.
* Joël Riou, *Formalization of derived categories in Lean/mathlib*, Ann. Formaliz. Math. 1 (2025),
  1–42, §5.3.4.

The descent uses Mathlib's `Localization.lift` and `Localization.liftNatTrans`; the derived
bifunctor uses `Functor.HasLeftDerivedFunctor₂` and `LocalizerMorphism.prod`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

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

universe w

section Braided

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]
  [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace CochainComplex.KFlat

/-- The product of the K-flat localizer morphism with itself derives the uncurried totalized tensor
product of cochain complexes followed by `DerivedCategory.Q`. -/
theorem prod_localizerMorphism_derives_tensor [HasDerivedCategory.{w} C] :
    ((localizerMorphism C).prod (localizerMorphism C)).Derives
      (Functor.uncurry.obj
        (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))) := by
  rw [LocalizerMorphism.Derives, LocalizerMorphism.prod_functor, localizerMorphism_functor]
  rintro ⟨K₁, L₁⟩ ⟨K₂, L₂⟩ f ⟨hf₁, hf₂⟩
  have : QuasiIso f.1.hom := (quasiIso_iff f.1).1 hf₁
  have : QuasiIso f.2.hom := (quasiIso_iff f.2).1 hf₂
  simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, ObjectProperty.ι_map,
    Functor.uncurry_obj_map, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
    Functor.whiskeringRight_obj_map, whiskerRight_app, MonoidalCategory.curriedTensor_obj_obj,
    MonoidalCategory.curriedTensor_map_app, MonoidalCategory.curriedTensor_obj_map,
    ObjectProperty.ι_obj]
  infer_instance

end CochainComplex.KFlat

namespace TauCeti

variable [HasDerivedCategory.{w} C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]

section Existence

variable (C) in
/-- **Existence of the derived tensor product.** When the inclusion of K-flat complexes
`CochainComplex.KFlat.localizerMorphism C` is a left derivability structure (for instance for
`C = ModuleCat R` over a commutative ring `R`), the totalized tensor product of cochain complexes
followed by `DerivedCategory.Q` admits a left derived bifunctor with respect to quasi-isomorphisms
in both variables. -/
theorem hasLeftDerivedFunctor₂_tensor :
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := C))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  have := (CochainComplex.KFlat.prod_localizerMorphism_derives_tensor
    (C := C)).hasPointwiseLeftDerivedFunctor
  infer_instance

attribute [instance] hasLeftDerivedFunctor₂_tensor

variable (C) in
/-- The left derived tensor product bifunctor `D(C) ⥤ D(C) ⥤ D(C)` on the unbounded derived
category of `C`. -/
def derivedTensor : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C :=
  Functor.leftDerived₂
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
    DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ))

variable (C) in
/-- The canonical counit comparison natural transformation exhibiting `TauCeti.derivedTensor C` as
a left derived bifunctor of the totalized tensor product of complexes. -/
def derivedTensorCounit :
    (((whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (derivedTensor C) ⟶
      MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)) :=
  Functor.leftDerivedCounit₂
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
    DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ))

instance :
    (derivedTensor C).IsLeftDerivedFunctor₂ (derivedTensorCounit C)
      (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)) := by
  dsimp only [derivedTensor, derivedTensorCounit]
  infer_instance

end Existence

section ModelComparison

variable (LF : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C)
  (α : (((whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
    DerivedCategory.Q).obj LF ⟶
      MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
  [LF.IsLeftDerivedFunctor₂ α
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ))]

private lemma isIso_app_app_of_isKFlat_both
    (P Q : CochainComplex C ℤ) [P.IsKFlat] [Q.IsKFlat] :
    IsIso ((α.app P).app Q) := by
  have h := (CochainComplex.KFlat.prod_localizerMorphism_derives_tensor (C := C)).isIso'
    (Functor.whiskeringLeft₂HomEquiv α)
    (L₂ := (DerivedCategory.Q (C := C)).prod DerivedCategory.Q)
    (CochainComplex.KFlat.mk P, CochainComplex.KFlat.mk Q)
  have heq : (((CochainComplex.KFlat.localizerMorphism C).prod
      (CochainComplex.KFlat.localizerMorphism C)).functor.obj
      (CochainComplex.KFlat.mk P, CochainComplex.KFlat.mk Q)) = (P, Q) := by
    simp
  rw [NatTrans.isIso_app_iff_of_iso (Functor.whiskeringLeft₂HomEquiv α) (eqToIso heq)] at h
  exact h

/-- For any left derived bifunctor `(LF, α)` of the tensor product, `(α.app P).app L` is an
isomorphism whenever `P` is K-flat, for every (possibly unbounded) complex `L`. -/
instance isIso_app_app_of_isKFlat_left_of_isLeftDerivedFunctor₂_tensor
    (P L : CochainComplex C ℤ) [P.IsKFlat] :
    IsIso ((α.app P).app L) := by
  obtain ⟨R⟩ : Nonempty ((CochainComplex.KFlat.localizerMorphism C).LeftResolution L) :=
    inferInstance
  obtain ⟨Q, π, hπ, hQ⟩ :
      ∃ (Q : CochainComplex C ℤ) (π : Q ⟶ L), QuasiIso π ∧ Q.IsKFlat :=
    ⟨_, R.w, (mem_quasiIso_iff R.w).1 R.hw, by
      rw [CochainComplex.KFlat.localizerMorphism_functor]
      exact (CochainComplex.kFlat_iff _).1 R.X₁.property⟩
  have : QuasiIso π := hπ
  have : Q.IsKFlat := hQ
  have := isIso_app_app_of_isKFlat_both LF α P Q
  have hnat := (α.app P).naturality π
  dsimp at hnat
  rw [← IsIso.eq_inv_comp] at hnat
  rw [hnat]
  infer_instance

/-- For any left derived bifunctor `(LF, α)` of the tensor product, `(α.app K).app Q` is an
isomorphism whenever `Q` is K-flat, for every (possibly unbounded) complex `K`. -/
instance isIso_app_app_of_isKFlat_right_of_isLeftDerivedFunctor₂_tensor
    (K Q : CochainComplex C ℤ) [Q.IsKFlat] :
    IsIso ((α.app K).app Q) := by
  obtain ⟨R⟩ : Nonempty ((CochainComplex.KFlat.localizerMorphism C).LeftResolution K) :=
    inferInstance
  obtain ⟨P, π, hπ, hP⟩ :
      ∃ (P : CochainComplex C ℤ) (π : P ⟶ K), QuasiIso π ∧ P.IsKFlat :=
    ⟨_, R.w, (mem_quasiIso_iff R.w).1 R.hw, by
      rw [CochainComplex.KFlat.localizerMorphism_functor]
      exact (CochainComplex.kFlat_iff _).1 R.X₁.property⟩
  have : QuasiIso π := hπ
  have : P.IsKFlat := hP
  have := isIso_app_app_of_isKFlat_both LF α P Q
  have hnat := NatTrans.congr_app (α.naturality π) Q
  dsimp at hnat
  rw [← IsIso.eq_inv_comp] at hnat
  rw [hnat]
  infer_instance

/-- For any complex `K` (without any K-flatness assumption), `LF.obj (Q.obj K)` is a left derived
functor of `K ⊗ - ⋙ Q` via `Functor.bifunctorCounit₁ α K`. -/
instance isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor
    (K : CochainComplex C ℤ) :
    (LF.obj (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor (Functor.bifunctorCounit₁ α K)
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  have hDerives : (CochainComplex.KFlat.localizerMorphism C).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj K ⋙ DerivedCategory.Q) := by
    rw [LocalizerMorphism.Derives, CochainComplex.KFlat.localizerMorphism_functor]
    intro Q₁ Q₂ g hg
    have : QuasiIso g.hom := (CochainComplex.KFlat.quasiIso_iff g).1 hg
    simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.ι_obj,
      MonoidalCategory.curriedTensor_obj_map]
    infer_instance
  refine hDerives.isLeftDerivedFunctor_of_isIso _ fun Q ↦ ?_
  rw [CochainComplex.KFlat.localizerMorphism_functor, ObjectProperty.ι_obj,
    Functor.bifunctorCounit₁_app]
  exact isIso_app_app_of_isKFlat_right_of_isLeftDerivedFunctor₂_tensor LF α K Q.obj

/-- For any complex `L` (without any K-flatness assumption), `LF.flip.obj (Q.obj L)` is a left
derived functor of `- ⊗ L ⋙ Q` via `Functor.bifunctorCounit₂ α L`. -/
instance isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor
    (L : CochainComplex C ℤ) :
    (LF.flip.obj (DerivedCategory.Q.obj L)).IsLeftDerivedFunctor (Functor.bifunctorCounit₂ α L)
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  have hDerives : (CochainComplex.KFlat.localizerMorphism C).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).flip.obj L ⋙
        DerivedCategory.Q) := by
    rw [LocalizerMorphism.Derives, CochainComplex.KFlat.localizerMorphism_functor]
    intro P₁ P₂ g hg
    have : QuasiIso g.hom := (CochainComplex.KFlat.quasiIso_iff g).1 hg
    simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.ι_obj, Functor.flip_obj_map,
      MonoidalCategory.curriedTensor_map_app]
    infer_instance
  refine hDerives.isLeftDerivedFunctor_of_isIso _ fun P ↦ ?_
  rw [CochainComplex.KFlat.localizerMorphism_functor, ObjectProperty.ι_obj,
    Functor.bifunctorCounit₂_app]
  exact isIso_app_app_of_isKFlat_left_of_isLeftDerivedFunctor₂_tensor LF α P.obj L

/-- When `P` is K-flat, the partial counit `Functor.bifunctorCounit₁ α P` is a natural isomorphism
`DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅ tensorLeft P ⋙ DerivedCategory.Q`. -/
instance isIso_bifunctorCounit₁_of_isKFlat_of_isLeftDerivedFunctor₂_tensor
    (P : CochainComplex C ℤ) [P.IsKFlat] :
    IsIso (Functor.bifunctorCounit₁ α P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro L
  rw [Functor.bifunctorCounit₁_app]
  exact isIso_app_app_of_isKFlat_left_of_isLeftDerivedFunctor₂_tensor LF α P L

/-- When `Q` is K-flat, the partial counit `Functor.bifunctorCounit₂ α Q` is a natural isomorphism
`DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q) ≅ tensorRight Q ⋙ DerivedCategory.Q`. -/
instance isIso_bifunctorCounit₂_of_isKFlat_of_isLeftDerivedFunctor₂_tensor
    (Q : CochainComplex C ℤ) [Q.IsKFlat] :
    IsIso (Functor.bifunctorCounit₂ α Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [Functor.bifunctorCounit₂_app]
  exact isIso_app_app_of_isKFlat_right_of_isLeftDerivedFunctor₂_tensor LF α K Q

/-- When `P` is bounded above with flat terms and sequential colimits in `C` are exact and commute
with tensoring, `Functor.bifunctorCounit₁ α P` is a natural isomorphism. -/
theorem isIso_bifunctorCounit₁_of_boundedAbove_flat_of_isLeftDerivedFunctor₂_tensor
    [∀ M : C, PreservesFiniteColimits (MonoidalCategory.tensorLeft M)]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (MonoidalCategory.tensorRight X)]
    (P : CochainComplex C ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X i))] :
    IsIso (Functor.bifunctorCounit₁ α P) :=
  have := P.isKFlat_of_boundedAbove_flat b
  inferInstance

/-- When `Q` is bounded above with flat terms and sequential colimits in `C` are exact and commute
with tensoring, `Functor.bifunctorCounit₂ α Q` is a natural isomorphism. -/
theorem isIso_bifunctorCounit₂_of_boundedAbove_flat_of_isLeftDerivedFunctor₂_tensor
    [∀ M : C, PreservesFiniteColimits (MonoidalCategory.tensorLeft M)]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (MonoidalCategory.tensorRight X)]
    (Q : CochainComplex C ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (Q.X i))] :
    IsIso (Functor.bifunctorCounit₂ α Q) :=
  have := Q.isKFlat_of_boundedAbove_flat b
  inferInstance

/-- For a K-flat complex `P`, evaluating any left derived tensor bifunctor `(LF, α)` at
`DerivedCategory.Q.obj P` is naturally isomorphic to `P.kFlatTensor`. -/
def leftDerivedTensorObjIsoKFlatTensor (P : CochainComplex C ℤ) [P.IsKFlat] :
    LF.obj (DerivedCategory.Q.obj P) ≅ P.kFlatTensor :=
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙ DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α P)⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙ DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj P) ⋙ DerivedCategory.Q)
    (LF.obj (DerivedCategory.Q.obj P)) P.kFlatTensor
    (Functor.isoWhiskerRight ((CochainComplex.curriedTensorIsoMap₂CochainComplex C).app P)
      DerivedCategory.Q)

/-- On a complex model `L`, `leftDerivedTensorObjIsoKFlatTensor LF α P` intertwines
`P.kFlatTensorModelIso` with `(α.app P).app L`. -/
@[reassoc (attr := simp)]
theorem leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp
    (P L : CochainComplex C ℤ) [P.IsKFlat] :
    (leftDerivedTensorObjIsoKFlatTensor LF α P).hom.app (DerivedCategory.Q.obj L) ≫
      P.kFlatTensorModelIso.hom.app L = (α.app P).app L := by
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙ DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α P)⟩
  have h := Localization.liftNatTrans_app DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
    ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙ DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj P) ⋙ DerivedCategory.Q)
    (LF.obj (DerivedCategory.Q.obj P)) P.kFlatTensor
    (Functor.isoWhiskerRight ((CochainComplex.curriedTensorIsoMap₂CochainComplex C).app P)
      DerivedCategory.Q).hom L
  rw [← CochainComplex.kFlatTensorModelIso_eq_liftingIso P] at h
  have h' := h =≫ P.kFlatTensorModelIso.hom.app L
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h'
  exact h'.trans (by dsimp [Functor.bifunctorCounit₁]; simp; rfl)

/-- Compatibility of `leftDerivedTensorObjIsoKFlatTensor` with morphisms `f : P₁ ⟶ P₂` between
K-flat models: `LF.map (DerivedCategory.Q.map f)` corresponds to `CochainComplex.kFlatTensorMap f`.
-/
@[reassoc]
theorem leftDerivedTensorObjIsoKFlatTensor_naturality
    {P₁ P₂ : CochainComplex C ℤ} [P₁.IsKFlat] [P₂.IsKFlat] (f : P₁ ⟶ P₂) :
    LF.map (DerivedCategory.Q.map f) ≫ (leftDerivedTensorObjIsoKFlatTensor LF α P₂).hom =
      (leftDerivedTensorObjIsoKFlatTensor LF α P₁).hom ≫ CochainComplex.kFlatTensorMap f := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) fun L ↦ ?_
  rw [← cancel_mono (P₂.kFlatTensorModelIso.hom.app L)]
  simp only [NatTrans.comp_app, Category.assoc, leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp,
    CochainComplex.kFlatTensorMap_app_Q_comp,
    leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp_assoc]
  have hnat := NatTrans.congr_app (α.naturality f) L
  dsimp at hnat
  rw [whiskerRight_eq_mapBifunctorMap] at hnat
  exact hnat

/-- **Left unitor.** Left derived tensoring with the monoidal unit complex `𝟙_ (CochainComplex C ℤ)`
(the unit of `C` in degree `0`) is naturally isomorphic to the identity of `DerivedCategory C`, for
any left derived tensor bifunctor `(LF, α)`. -/
def leftDerivedTensorLeftUnitor :
    LF.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≅ 𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C))
    (LF.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ)))) (𝟭 (DerivedCategory C))
    (asIso (Functor.bifunctorCounit₁ α (𝟙_ (CochainComplex C ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `leftDerivedTensorLeftUnitor` is the derived tensor counit followed by the
left unitor of `CochainComplex C ℤ`. -/
@[simp]
theorem leftDerivedTensorLeftUnitor_hom_app_Q (L : CochainComplex C ℤ) :
    (leftDerivedTensorLeftUnitor LF α).hom.app (DerivedCategory.Q.obj L) =
      (α.app (𝟙_ (CochainComplex C ℤ))).app L ≫ DerivedCategory.Q.map (λ_ L).hom := by
  simp [leftDerivedTensorLeftUnitor]

/-- **Right unitor.** Right derived tensoring with the monoidal unit complex
`𝟙_ (CochainComplex C ℤ)` is naturally isomorphic to the identity of `DerivedCategory C`, for any
left derived tensor bifunctor `(LF, α)`. -/
def leftDerivedTensorRightUnitor :
    LF.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≅ 𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C))
    (LF.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ)))) (𝟭 (DerivedCategory C))
    (asIso (Functor.bifunctorCounit₂ α (𝟙_ (CochainComplex C ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.rightUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `leftDerivedTensorRightUnitor` is the derived tensor counit followed by the
right unitor of `CochainComplex C ℤ`. -/
@[simp]
theorem leftDerivedTensorRightUnitor_hom_app_Q (K : CochainComplex C ℤ) :
    (leftDerivedTensorRightUnitor LF α).hom.app (DerivedCategory.Q.obj K) =
      (α.app K).app (𝟙_ (CochainComplex C ℤ)) ≫ DerivedCategory.Q.map (ρ_ K).hom := by
  simp [leftDerivedTensorRightUnitor]

end ModelComparison

end TauCeti

end Braided
