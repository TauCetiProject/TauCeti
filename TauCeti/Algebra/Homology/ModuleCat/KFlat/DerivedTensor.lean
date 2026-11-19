/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Tensor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
public import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.Category.ModuleCat.AB
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Derived tensor products on unbounded module derived categories

Over a commutative ring `R`, the external product of the K-flat left derivability structure
`CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)` with itself is a left derivability
structure on pairs of cochain complexes, and it derives the totalized tensor product bifunctor
followed by `DerivedCategory.Q` because tensoring with a K-flat complex on either side preserves
quasi-isomorphisms. Consequently, the tensor product bifunctor admits a left derived bifunctor
(`TauCeti.hasLeftDerivedFunctor₂_tensor`, `TauCeti.derivedTensor`) on the unbounded derived category
`DerivedCategory (ModuleCat.{u} R)`.

For any left derived bifunctor `(LF, α)` of the tensor product:
* the partial evaluations `LF.obj (DerivedCategory.Q.obj K)` and
  `LF.flip.obj (DerivedCategory.Q.obj L)` are left derived functors of `K ⊗ -` and `- ⊗ L` via
  `Functor.bifunctorCounit₁ α K` and `Functor.bifunctorCounit₂ α L` for every complex `K` and `L`;
* the comparison `(α.app P).app L` is an isomorphism whenever either `P` or `L` is K-flat — without
  any K-flatness or boundedness assumption on the other factor;
* for K-flat `P`, `LF.obj (DerivedCategory.Q.obj P)` is naturally isomorphic to `P.kFlatTensor`
  compatibly with morphisms of K-flat models;
* for bounded-above complexes of flat `R`-modules on either side, the derived tensor product on
  complex models is naturally isomorphic to the ordinary totalized tensor product followed by
  `DerivedCategory.Q` (`TauCeti.leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat`,
  `TauCeti.leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat`).

## Main definitions

* `TauCeti.derivedTensor`, `TauCeti.derivedTensorCounit`: the left derived tensor bifunctor
  `D(R) ⥤ D(R) ⥤ D(R)` on the unbounded derived category of `R`-modules and its comparison
  natural transformation.
* `TauCeti.leftDerivedTensorObjIsoKFlatTensor`: for K-flat `P`, the natural isomorphism identifying
  `LF.obj (DerivedCategory.Q.obj P)` with `P.kFlatTensor`.
* `TauCeti.leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat`,
  `TauCeti.leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat`: for a bounded-above complex of flat
  `R`-modules in the left or right variable, the natural isomorphism between the derived tensor
  functor on complex models and the ordinary totalized tensor functor followed by `Q`.

## Main results

* `TauCeti.hasLeftDerivedFunctor₂_tensor`: the totalized tensor product of complexes of
  `R`-modules followed by `DerivedCategory.Q` has a left derived bifunctor.
* `TauCeti.isIso_app_app_of_isKFlat_left_of_isLeftDerivedFunctor₂_tensor`,
  `TauCeti.isIso_app_app_of_isKFlat_right_of_isLeftDerivedFunctor₂_tensor`: the derived tensor
  comparison `(α.app P).app L` is an isomorphism whenever either `P` or `L` is K-flat.
* `TauCeti.isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor`,
  `TauCeti.isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor`: partial
  evaluation of any left derived tensor bifunctor at `DerivedCategory.Q.obj K` (or `.flip` at
  `DerivedCategory.Q.obj L`) is a left derived functor of `K ⊗ -` (or `- ⊗ L`).
* `TauCeti.leftDerivedTensorObjIsoKFlatTensor_naturality`: compatibility of the K-flat model
  identification with morphisms between K-flat complexes.

## References

* [The Stacks Project][stacks], Section 15.60, Lemma 15.60.12 (Tag 064L) and
  Definition 15.60.13 (Tag 064M).
* Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008),
  1286–1318.
* Joël Riou, *Formalization of derived categories in Lean/mathlib*, Ann. Formaliz. Math. 1 (2025),
  1–42, §5.3.4, and the Mathlib modules
  `Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product` and
  `Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo`, which formalize external products of
  derivability structures and left derived bifunctors.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor Limits HomologicalComplex
open scoped MonoidalCategory

universe u w

namespace CochainComplex.KFlat

variable {R : Type u} [CommRing R]

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
  infer_instance

end CochainComplex.KFlat

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
instance isIso_app_app_of_isKFlat_left_of_isLeftDerivedFunctor₂_tensor
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso ((α.app P).app L) := by
  obtain ⟨Q, π, hπ, hQ⟩ := L.exists_quasiIso_isKFlat_moduleCat
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
    (K Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat] :
    IsIso ((α.app K).app Q) := by
  obtain ⟨P, π, hπ, hP⟩ := K.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso π := hπ
  have : P.IsKFlat := hP
  have := isIso_app_app_of_isKFlat_both LF α P Q
  have hnat := NatTrans.congr_app (α.naturality π) Q
  dsimp at hnat
  rw [← IsIso.eq_inv_comp] at hnat
  rw [hnat]
  infer_instance

/-- For any complex `K` of `R`-modules (without any K-flatness assumption), `LF.obj (Q.obj K)` is a
left derived functor of `K ⊗ - ⋙ Q` via `Functor.bifunctorCounit₁ α K`. -/
instance isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (LF.obj (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor (Functor.bifunctorCounit₁ α K)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have hDerives : (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj K ⋙
        DerivedCategory.Q) := by
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

/-- For any complex `L` of `R`-modules (without any K-flatness assumption),
`LF.flip.obj (Q.obj L)` is a left derived functor of `- ⊗ L ⋙ Q` via
`Functor.bifunctorCounit₂ α L`. -/
instance isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (LF.flip.obj (DerivedCategory.Q.obj L)).IsLeftDerivedFunctor (Functor.bifunctorCounit₂ α L)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have hDerives : (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).flip.obj L ⋙
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
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso (Functor.bifunctorCounit₁ α P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro L
  rw [Functor.bifunctorCounit₁_app]
  exact isIso_app_app_of_isKFlat_left_of_isLeftDerivedFunctor₂_tensor LF α P L

/-- When `Q` is K-flat, the partial counit `Functor.bifunctorCounit₂ α Q` is a natural isomorphism
`DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q) ≅ tensorRight Q ⋙ DerivedCategory.Q`. -/
instance isIso_bifunctorCounit₂_of_isKFlat_of_isLeftDerivedFunctor₂_tensor
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat] :
    IsIso (Functor.bifunctorCounit₂ α Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [Functor.bifunctorCounit₂_app]
  exact isIso_app_app_of_isKFlat_right_of_isLeftDerivedFunctor₂_tensor LF α K Q

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
  have := isIso_bifunctorCounit₁_of_isKFlat_of_isLeftDerivedFunctor₂_tensor LF α P
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
  have := isIso_bifunctorCounit₁_of_isKFlat_of_isLeftDerivedFunctor₂_tensor LF α P
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
