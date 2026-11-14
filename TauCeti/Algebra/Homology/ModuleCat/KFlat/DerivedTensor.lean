/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Tensor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Derived tensor products on unbounded module derived categories

Over a commutative ring `R`, the free-forgetful adjunction on `ModuleCat.{u} R` furnishes a
functorial epimorphic cover of every `R`-module by a free (hence flat) `R`-module. Together with
exactness of countable coproducts and sequential colimits in `ModuleCat.{u} R`, this makes the
inclusion localizer morphism `CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)` a left
derivability structure on unbounded cochain complexes with respect to quasi-isomorphisms.

Its external product with itself is therefore a left derivability structure on pairs of complexes,
and it derives the totalized tensor product bifunctor followed by `DerivedCategory.Q` because
tensoring with a K-flat complex on either side preserves quasi-isomorphisms. Consequently, the
tensor product bifunctor admits a left derived bifunctor (`TauCeti.hasLeftDerivedFunctor₂_tensor`,
`TauCeti.derivedTensor`) on the unbounded derived category `DerivedCategory (ModuleCat.{u} R)`.

For any left derived bifunctor `(LF, α)` of the tensor product, the comparison `(α.app P).app L` is
an isomorphism whenever either `P` or `L` is K-flat — without any K-flatness or boundedness
assumption on the other factor. In particular, for K-flat `P` (including every bounded-above
complex of flat `R`-modules), `LF.obj (DerivedCategory.Q.obj P)` is naturally isomorphic to
`P.kFlatTensor`, compatibly with morphisms of K-flat models, so `P ⊗^L L` is computed naturally by
the ordinary total tensor product `P ⊗ L`.

## Main definitions

* `TauCeti.derivedTensor`, `TauCeti.derivedTensorCounit`: the left derived tensor bifunctor
  `D(R) ⥤ D(R) ⥤ D(R)` on the unbounded derived category of `R`-modules and its comparison
  natural transformation.
* `TauCeti.leftDerivedTensorObjIsoKFlatTensor`: for K-flat `P`, the natural isomorphism identifying
  `LF.obj (DerivedCategory.Q.obj P)` with `P.kFlatTensor`.
* `TauCeti.boundedAboveFlatTensorIso`: for a bounded-above complex `P` of flat `R`-modules, the
  natural isomorphism `DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅ tensorLeft P ⋙ Q`.

## Main results

* `CochainComplex.KFlat.instIsLeftDerivabilityStructureLocalizerMorphismModuleCat`: the K-flat
  localizer morphism on `CochainComplex (ModuleCat.{u} R) ℤ` is a left derivability structure.
* `TauCeti.hasLeftDerivedFunctor₂_tensor`: the totalized tensor product of complexes of
  `R`-modules followed by `DerivedCategory.Q` has a left derived bifunctor.
* `TauCeti.isIso_app_app_of_isKFlat_left`, `TauCeti.isIso_app_app_of_isKFlat_right`: the derived
  tensor comparison `(α.app P).app L` is an isomorphism whenever either `P` or `L` is K-flat.
* `TauCeti.leftDerivedTensorObjIsoKFlatTensor_naturality`: compatibility of the K-flat model
  identification with morphisms between K-flat complexes.

## References

* The Stacks Project, More on Algebra, Section 15.60, Lemma 15.60.12 (Tag 064L) and
  Definition 15.60.13 (Tag 064M).
* Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008),
  1286–1318.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor Limits HomologicalComplex
open scoped MonoidalCategory

universe u w

namespace CochainComplex

section ModuleCat

variable {R : Type u} [CommRing R]

private instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE.{0, 0, u, u} _

/-- A bounded-above complex of flat `R`-modules is K-flat. -/
theorem isKFlat_of_isStrictlyLE_flat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] :
    K.IsKFlat :=
  K.isKFlat_of_boundedAbove_flat b

namespace KFlat

private instance (X : ModuleCat.{u} R) :
    Epi ((ModuleCat.adj.{u} R).counit.app X) :=
  inferInstanceAs (Epi ((ModuleCat.projectiveResolution R).π.app X))

private instance (X : ModuleCat.{u} R) :
    PreservesFiniteLimits (MonoidalCategory.tensorLeft
      ((CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R).obj X)) :=
  inferInstanceAs (PreservesFiniteLimits (MonoidalCategory.tensorLeft
    (ModuleCat.of R ((CategoryTheory.forget (ModuleCat.{u} R)).obj X →₀ R))))

instance instHasLeftResolutionsArrowLocalizerMorphismModuleCat :
    (localizerMorphism (ModuleCat.{u} R)).arrow.HasLeftResolutions :=
  hasLeftResolutions_arrow_localizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R)
    (ModuleCat.adj.{u} R).counit

instance instIsLocalizedEquivalenceLocalizerMorphismModuleCat :
    (localizerMorphism (ModuleCat.{u} R)).IsLocalizedEquivalence :=
  isLocalizedEquivalence_localizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R)
    (ModuleCat.adj.{u} R).counit

instance instIsConnectedLeftResolutionLocalizerMorphismModuleCat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsConnected ((localizerMorphism (ModuleCat.{u} R)).LeftResolution K) :=
  isConnected_leftResolution_localizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R)
    (ModuleCat.adj.{u} R).counit K

/-- Over a commutative ring `R`, the inclusion of K-flat cochain complexes into all cochain
complexes of `R`-modules is a left derivability structure with respect to quasi-isomorphisms. -/
instance instIsLeftDerivabilityStructureLocalizerMorphismModuleCat :
    (localizerMorphism (ModuleCat.{u} R)).IsLeftDerivabilityStructure :=
  isLeftDerivabilityStructure_localizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R)
    (ModuleCat.adj.{u} R).counit

/-- The product of the K-flat localizer morphism with itself derives the uncurried tensor product
of complexes of `R`-modules followed by `DerivedCategory.Q`. -/
theorem prod_localizerMorphism_derives_tensor [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    ((localizerMorphism (ModuleCat.{u} R)).prod
      (localizerMorphism (ModuleCat.{u} R))).Derives
      (Functor.uncurry.obj
        (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj
            (DerivedCategory.Q (C := ModuleCat.{u} R)))) := by
  rw [LocalizerMorphism.Derives, LocalizerMorphism.prod_functor, localizerMorphism_functor]
  rintro ⟨K₁, L₁⟩ ⟨K₂, L₂⟩ f ⟨hf₁, hf₂⟩
  have : QuasiIso f.1.hom := (quasiIso_iff f.1).1 hf₁
  have : QuasiIso f.2.hom := (quasiIso_iff f.2).1 hf₂
  simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, ObjectProperty.ι_map,
    Functor.uncurry_obj_map, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
    Functor.whiskeringRight_obj_map, whiskerRight_app, MonoidalCategory.curriedTensor_obj_obj,
    MonoidalCategory.curriedTensor_map_app, MonoidalCategory.curriedTensor_obj_map,
    ObjectProperty.ι_obj]
  have h₁ : IsIso (DerivedCategory.Q.map (f.1.hom ▷ L₁.obj)) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (tensorHom f.1.hom (𝟙 L₁.obj))))
  have h₂ : IsIso (DerivedCategory.Q.map (K₂.obj ◁ f.2.hom)) := by
    rw [whiskerLeft_eq_mapBifunctorMap]
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (tensorHom (𝟙 K₂.obj) f.2.hom)))
  infer_instance

end KFlat

end ModuleCat

end CochainComplex

namespace TauCeti

section Existence

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- **Existence of the derived tensor product.** Over a commutative ring `R`, the totalized tensor
product of cochain complexes of `R`-modules followed by `DerivedCategory.Q` admits a left derived
bifunctor with respect to quasi-isomorphisms in both variables. -/
theorem hasLeftDerivedFunctor₂_tensor :
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := ModuleCat.{u} R))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have := (CochainComplex.KFlat.prod_localizerMorphism_derives_tensor
    (R := R)).hasPointwiseLeftDerivedFunctor
  infer_instance

attribute [instance] hasLeftDerivedFunctor₂_tensor

/-- The left derived tensor product bifunctor `D(R) ⥤ D(R) ⥤ D(R)` on the unbounded derived
category of `R`-modules. -/
def derivedTensor :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) :=
  Functor.leftDerived₂
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))
    DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))

/-- The canonical counit comparison natural transformation exhibiting `TauCeti.derivedTensor R` as
a left derived bifunctor of the totalized tensor product of complexes. -/
def derivedTensorCounit :
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (derivedTensor R) ⟶
      MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
  Functor.leftDerivedCounit₂
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))
    DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))

instance :
    (derivedTensor R).IsLeftDerivedFunctor₂ (derivedTensorCounit R)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  dsimp only [derivedTensor, derivedTensorCounit]
  infer_instance

end Existence

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

private lemma isIso_app_app_of_isKFlat_both
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] [Q.IsKFlat] :
    IsIso ((α.app P).app Q) := by
  have h := (CochainComplex.KFlat.prod_localizerMorphism_derives_tensor (R := R)).isIso'
    (Functor.whiskeringLeft₂HomEquiv α)
    (L₂ := (DerivedCategory.Q (C := ModuleCat.{u} R)).prod DerivedCategory.Q)
    (CochainComplex.KFlat.mk P, CochainComplex.KFlat.mk Q)
  have heq : (((CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).prod
      (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R))).functor.obj
      (CochainComplex.KFlat.mk P, CochainComplex.KFlat.mk Q)) = (P, Q) := by
    simp
  rw [NatTrans.isIso_app_iff_of_iso (Functor.whiskeringLeft₂HomEquiv α) (eqToIso heq)] at h
  exact h

/-- For any left derived bifunctor `(LF, α)` of the tensor product, `(α.app P).app L` is an
isomorphism whenever `P` is K-flat, for every (possibly unbounded) complex `L`. -/
instance isIso_app_app_of_isKFlat_left
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso ((α.app P).app L) := by
  obtain ⟨Q, π, hπ, hQ⟩ := L.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso π := hπ
  have : Q.IsKFlat := hQ
  have := isIso_app_app_of_isKFlat_both LF α P Q
  have hnat := (α.app P).naturality π
  dsimp at hnat
  have : IsIso (DerivedCategory.Q.map (P ◁ π)) := by
    rw [whiskerLeft_eq_mapBifunctorMap]
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (tensorHom (𝟙 P) π)))
  rw [← IsIso.eq_inv_comp] at hnat
  rw [hnat]
  infer_instance

/-- For any left derived bifunctor `(LF, α)` of the tensor product, `(α.app K).app Q` is an
isomorphism whenever `Q` is K-flat, for every (possibly unbounded) complex `K`. -/
instance isIso_app_app_of_isKFlat_right
    (K Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat] :
    IsIso ((α.app K).app Q) := by
  obtain ⟨P, π, hπ, hP⟩ := K.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso π := hπ
  have : P.IsKFlat := hP
  have := isIso_app_app_of_isKFlat_both LF α P Q
  have hnat := NatTrans.congr_app (α.naturality π) Q
  dsimp at hnat
  have : IsIso (DerivedCategory.Q.map (π ▷ Q)) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (tensorHom π (𝟙 Q))))
  rw [← IsIso.eq_inv_comp] at hnat
  rw [hnat]
  infer_instance

/-- When `P` is K-flat, the partial counit `Functor.bifunctorCounit₁ α P` is a natural isomorphism
`DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅ tensorLeft P ⋙ DerivedCategory.Q`. -/
instance isIso_bifunctorCounit₁_of_isKFlat
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso (Functor.bifunctorCounit₁ α P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro L
  rw [Functor.bifunctorCounit₁_app]
  infer_instance

/-- When `Q` is K-flat, the partial counit `Functor.bifunctorCounit₂ α Q` is a natural isomorphism
`DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q) ≅ tensorRight Q ⋙ DerivedCategory.Q`. -/
instance isIso_bifunctorCounit₂_of_isKFlat
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat] :
    IsIso (Functor.bifunctorCounit₂ α Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [Functor.bifunctorCounit₂_app]
  infer_instance

private def modelCompIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj P ⋙
      DerivedCategory.Q) ≅
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P ⋙
      DerivedCategory.Q) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [whiskerLeft_eq_mapBifunctorMap]

/-- For a K-flat complex `P` of `R`-modules, evaluating any left derived tensor bifunctor `(LF, α)`
at `DerivedCategory.Q.obj P` is naturally isomorphic to `P.kFlatTensor`. -/
def leftDerivedTensorObjIsoKFlatTensor
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    LF.obj (DerivedCategory.Q.obj P) ≅ P.kFlatTensor := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj P ⋙
        DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α P)⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    ((MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj P ⋙
      DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P) ⋙
      DerivedCategory.Q)
    (LF.obj (DerivedCategory.Q.obj P)) P.kFlatTensor (modelCompIso P)

/-- On a complex model `L`, `leftDerivedTensorObjIsoKFlatTensor LF α P` intertwines
`P.kFlatTensorModelIso` with `(α.app P).app L`. -/
@[reassoc (attr := simp)]
theorem leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (leftDerivedTensorObjIsoKFlatTensor LF α P).hom.app (DerivedCategory.Q.obj L) ≫
      P.kFlatTensorModelIso.hom.app L = (α.app P).app L := by
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj P ⋙
        DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α P)⟩
  have h := Localization.liftNatTrans_app DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    ((MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj P ⋙
      DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P) ⋙
      DerivedCategory.Q)
    (LF.obj (DerivedCategory.Q.obj P)) P.kFlatTensor (modelCompIso P).hom L
  rw [← CochainComplex.kFlatTensorModelIso_eq_liftingIso P] at h
  have h' := h =≫ P.kFlatTensorModelIso.hom.app L
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h'
  exact h'.trans (by dsimp [modelCompIso, Functor.bifunctorCounit₁]; exact Category.comp_id _)

/-- Compatibility of `leftDerivedTensorObjIsoKFlatTensor` with morphisms `f : P₁ ⟶ P₂` between
K-flat models: `LF.map (DerivedCategory.Q.map f)` corresponds to `CochainComplex.kFlatTensorMap f`.
-/
@[reassoc]
theorem leftDerivedTensorObjIsoKFlatTensor_naturality
    {P₁ P₂ : CochainComplex (ModuleCat.{u} R) ℤ} [P₁.IsKFlat] [P₂.IsKFlat] (f : P₁ ⟶ P₂) :
    LF.map (DerivedCategory.Q.map f) ≫ (leftDerivedTensorObjIsoKFlatTensor LF α P₂).hom =
      (leftDerivedTensorObjIsoKFlatTensor LF α P₁).hom ≫ CochainComplex.kFlatTensorMap f := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
  intro L
  rw [← cancel_mono (P₂.kFlatTensorModelIso.hom.app L)]
  have h₁ : ((LF.map (DerivedCategory.Q.map f) ≫
      (leftDerivedTensorObjIsoKFlatTensor LF α P₂).hom).app (DerivedCategory.Q.obj L)) ≫
      P₂.kFlatTensorModelIso.hom.app L =
      (LF.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫ (α.app P₂).app L :=
    (Category.assoc _ _ _).trans
      (congrArg ((LF.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫ ·)
        (leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp LF α P₂ L))
  have h₂a : (((leftDerivedTensorObjIsoKFlatTensor LF α P₁).hom ≫
      CochainComplex.kFlatTensorMap f).app (DerivedCategory.Q.obj L)) ≫
      P₂.kFlatTensorModelIso.hom.app L =
      (leftDerivedTensorObjIsoKFlatTensor LF α P₁).hom.app (DerivedCategory.Q.obj L) ≫
      P₁.kFlatTensorModelIso.hom.app L ≫ DerivedCategory.Q.map (tensorHom f (𝟙 L)) := by
    rw [NatTrans.comp_app, Category.assoc, CochainComplex.kFlatTensorMap_app_Q_comp]
    rfl
  have h₂ : (((leftDerivedTensorObjIsoKFlatTensor LF α P₁).hom ≫
      CochainComplex.kFlatTensorMap f).app (DerivedCategory.Q.obj L)) ≫
      P₂.kFlatTensorModelIso.hom.app L =
      (α.app P₁).app L ≫ DerivedCategory.Q.map (tensorHom f (𝟙 L)) :=
    h₂a.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ DerivedCategory.Q.map (tensorHom f (𝟙 L)))
        (leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp LF α P₁ L)))
  have hnat := NatTrans.congr_app (α.naturality f) L
  dsimp at hnat
  rw [whiskerRight_eq_mapBifunctorMap] at hnat
  exact h₁.trans (hnat.trans h₂.symm)

/-- **Bounded-above flat models compute derived tensor products.** If `P` is a bounded-above
complex of flat `R`-modules, then `P ⊗^L -` on complex models is naturally isomorphic to the
ordinary totalized tensor product `P ⊗ -` followed by `DerivedCategory.Q`. -/
def boundedAboveFlatTensorIso
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Module.Flat R (P.X i)] :
    DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅
      (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj P ⋙
        DerivedCategory.Q := by
  have : P.IsKFlat := P.isKFlat_of_isStrictlyLE_flat b
  exact asIso (Functor.bifunctorCounit₁ α P)

@[simp]
theorem boundedAboveFlatTensorIso_hom_app
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Module.Flat R (P.X i)]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (boundedAboveFlatTensorIso LF α P b).hom.app L = (α.app P).app L := by
  have : P.IsKFlat := P.isKFlat_of_isStrictlyLE_flat b
  simp [boundedAboveFlatTensorIso]

end ModelComparison

end TauCeti
