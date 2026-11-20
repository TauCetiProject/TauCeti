/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Tensor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product

/-!
# Derived tensor products on unbounded derived categories

Let `C` be a braided monoidal abelian category satisfying the hypotheses of Mathlib's totalized
monoidal structure on cochain complexes, in which the K-flat complexes form a left derivability
structure `CochainComplex.KFlat.localizerMorphism C` (for instance when `C` has a functorial flat
epimorphic cover, by `CochainComplex.KFlat.isLeftDerivabilityStructure_localizerMorphism`). The
external product of this derivability structure with itself is a left derivability structure on
pairs of cochain complexes, and it derives the totalized tensor product bifunctor followed by
`DerivedCategory.Q` because tensoring with a K-flat complex on either side preserves
quasi-isomorphisms. Consequently, the tensor product bifunctor admits a left derived bifunctor
(`TauCeti.hasLeftDerivedFunctor₂_tensor`, `TauCeti.derivedTensor`) on the unbounded derived
category `DerivedCategory C`. Modules over a commutative ring and sheaves of modules over a sheaf of
commutative rings on a small site are the main examples.

For any left derived bifunctor `(LF, α)` of the tensor product:
* the partial evaluations `LF.obj (DerivedCategory.Q.obj K)` and
  `LF.flip.obj (DerivedCategory.Q.obj L)` are left derived functors of `K ⊗ -` and `- ⊗ L` via
  `Functor.bifunctorCounit₁ α K` and `Functor.bifunctorCounit₂ α L` for every complex `K` and `L`;
* the comparison `(α.app P).app L` is an isomorphism whenever either `P` or `L` is K-flat — without
  any K-flatness or boundedness assumption on the other factor;
* for K-flat `P`, `LF.obj (DerivedCategory.Q.obj P)` is naturally isomorphic to `P.kFlatTensor`
  compatibly with morphisms of K-flat models;
* for bounded-above complexes of flat objects on either side, the derived tensor product on
  complex models is naturally isomorphic to the ordinary totalized tensor product followed by
  `DerivedCategory.Q` (`TauCeti.leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat`,
  `TauCeti.leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat`).

The unit `𝟙_ C` placed in degree `0` is a unit for the derived tensor product on both sides
(`TauCeti.derivedTensorLeftUnitor`, `TauCeti.derivedTensorRightUnitor`).

## Main definitions

* `TauCeti.derivedTensor`, `TauCeti.derivedTensorCounit`: the left derived tensor bifunctor
  `D(C) ⥤ D(C) ⥤ D(C)` on the unbounded derived category and its comparison natural
  transformation.
* `TauCeti.derivedTensorLeftUnitor`, `TauCeti.derivedTensorRightUnitor`: the natural isomorphisms
  `𝟙_ C[0] ⊗^L K ≅ K` and `K ⊗^L 𝟙_ C[0] ≅ K`.
* `TauCeti.leftDerivedTensorObjIsoKFlatTensor`: for K-flat `P`, the natural isomorphism identifying
  `LF.obj (DerivedCategory.Q.obj P)` with `P.kFlatTensor`.
* `TauCeti.leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat`,
  `TauCeti.leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat`: for a bounded-above complex of flat
  objects in the left or right variable, the natural isomorphism between the derived tensor
  functor on complex models and the ordinary totalized tensor functor followed by `Q`.

## Main results

* `TauCeti.hasLeftDerivedFunctor₂_tensor`: the totalized tensor product of complexes followed by
  `DerivedCategory.Q` has a left derived bifunctor.
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

universe w

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]
  [∀ (X Y : GradedObject ℤ C), GradedObject.HasTensor X Y]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X)]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

namespace CochainComplex.KFlat

variable [(localizerMorphism C).HasLeftResolutions]

/-- The product of the K-flat localizer morphism with itself derives the uncurried tensor product
of complexes followed by `DerivedCategory.Q`. -/
theorem prod_localizerMorphism_derives_tensor [HasDerivedCategory.{w} C] :
    ((localizerMorphism C).prod
      (localizerMorphism C)).Derives
      (Functor.uncurry.obj
        (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj
            (DerivedCategory.Q (C := C)))) := by
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

variable (C) [HasDerivedCategory.{w} C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]

/-- **Existence of the derived tensor product.** When the K-flat complexes form a left derivability
structure, the totalized tensor product of cochain complexes followed by `DerivedCategory.Q` admits
a left derived bifunctor with respect to quasi-isomorphisms in both variables. -/
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

/-- The left derived tensor product bifunctor `D(C) ⥤ D(C) ⥤ D(C)` on the unbounded derived
category, computed by K-flat resolutions of either factor. -/
def derivedTensor :
    DerivedCategory C ⥤
      DerivedCategory C ⥤
        DerivedCategory C :=
  Functor.leftDerived₂
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
    DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ))

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
    (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ))

instance :
    (derivedTensor C).IsLeftDerivedFunctor₂ (derivedTensorCounit C)
      (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  dsimp only [derivedTensor, derivedTensorCounit]
  infer_instance

end Existence

section ModelComparison

variable [HasDerivedCategory.{w} C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
variable (LF : DerivedCategory C ⥤
    DerivedCategory C ⥤ DerivedCategory C)
  (α : (((whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
    DerivedCategory.Q).obj LF ⟶
      MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
  [LF.IsLeftDerivedFunctor₂ α
    (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ))]

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
  obtain ⟨Q, π, hπ, hQ⟩ := L.exists_quasiIso_isKFlat_of_hasLeftResolutions
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
  obtain ⟨P, π, hπ, hP⟩ := K.exists_quasiIso_isKFlat_of_hasLeftResolutions
  have : QuasiIso π := hπ
  have : P.IsKFlat := hP
  have := isIso_app_app_of_isKFlat_both LF α P Q
  have hnat := NatTrans.congr_app (α.naturality π) Q
  dsimp at hnat
  rw [← IsIso.eq_inv_comp] at hnat
  rw [hnat]
  infer_instance

/-- For any complex `K` (without any K-flatness assumption), `LF.obj (Q.obj K)` is a
left derived functor of `K ⊗ - ⋙ Q` via `Functor.bifunctorCounit₁ α K`. -/
instance isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor
    (K : CochainComplex C ℤ) :
    (LF.obj (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor (Functor.bifunctorCounit₁ α K)
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  have hDerives : (CochainComplex.KFlat.localizerMorphism C).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj K ⋙
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

/-- For any complex `L` (without any K-flatness assumption),
`LF.flip.obj (Q.obj L)` is a left derived functor of `- ⊗ L ⋙ Q` via
`Functor.bifunctorCounit₂ α L`. -/
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

private def modelCompIso (P : CochainComplex C ℤ) :
    ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙
      DerivedCategory.Q) ≅
    ((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj P ⋙
      DerivedCategory.Q) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [whiskerLeft_eq_mapBifunctorMap]

/-- For a K-flat complex `P`, evaluating any left derived tensor bifunctor `(LF, α)`
at `DerivedCategory.Q.obj P` is naturally isomorphic to `P.kFlatTensor`. -/
def leftDerivedTensorObjIsoKFlatTensor
    (P : CochainComplex C ℤ) [P.IsKFlat] :
    LF.obj (DerivedCategory.Q.obj P) ≅ P.kFlatTensor := by
  have := isIso_bifunctorCounit₁_of_isKFlat_of_isLeftDerivedFunctor₂_tensor LF α P
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙
        DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α P)⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
    ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙
      DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj P) ⋙
      DerivedCategory.Q)
    (LF.obj (DerivedCategory.Q.obj P)) P.kFlatTensor (modelCompIso P)

/-- On a complex model `L`, `leftDerivedTensorObjIsoKFlatTensor LF α P` intertwines
`P.kFlatTensorModelIso` with `(α.app P).app L`. -/
@[reassoc (attr := simp)]
theorem leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp
    (P L : CochainComplex C ℤ) [P.IsKFlat] :
    (leftDerivedTensorObjIsoKFlatTensor LF α P).hom.app (DerivedCategory.Q.obj L) ≫
      P.kFlatTensorModelIso.hom.app L = (α.app P).app L := by
  have := isIso_bifunctorCounit₁_of_isKFlat_of_isLeftDerivedFunctor₂_tensor LF α P
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙
        DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α P)⟩
  have h := Localization.liftNatTrans_app DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
    ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙
      DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj P) ⋙
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
    {P₁ P₂ : CochainComplex C ℤ} [P₁.IsKFlat] [P₂.IsKFlat] (f : P₁ ⟶ P₂) :
    LF.map (DerivedCategory.Q.map f) ≫ (leftDerivedTensorObjIsoKFlatTensor LF α P₂).hom =
      (leftDerivedTensorObjIsoKFlatTensor LF α P₁).hom ≫ CochainComplex.kFlatTensorMap f := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
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

section BoundedAboveFlat

variable [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  [∀ X : C, PreservesColimitsOfShape ℕ (MonoidalCategory.tensorRight X)]
  [∀ X : C, PreservesFiniteColimits (MonoidalCategory.tensorLeft X)]

/-- **Bounded-above flat models compute derived tensor products in the left variable.** If `P` is a
bounded-above complex of flat objects, then
`DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P)` is naturally isomorphic to the ordinary
totalized tensor functor `P ⊗ -` followed by `DerivedCategory.Q`. -/
def leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat
    (P : CochainComplex C ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X i))] :
    DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅
      (MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙
        DerivedCategory.Q := by
  have : P.IsKFlat := P.isKFlat_of_boundedAbove_flat b
  exact asIso (Functor.bifunctorCounit₁ α P)

/-- The forward natural transformation of `leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat` is
`Functor.bifunctorCounit₁ α P`. -/
@[simp]
theorem leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat_hom
    (P : CochainComplex C ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X i))] :
    (leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat LF α P b).hom =
      Functor.bifunctorCounit₁ α P := by
  have : P.IsKFlat := P.isKFlat_of_boundedAbove_flat b
  simp [leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat]

/-- **Bounded-above flat models compute derived tensor products in the right variable.** If `Q` is
a bounded-above complex of flat objects, then
`DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q)` is naturally isomorphic to the ordinary
totalized tensor functor `- ⊗ Q` followed by `DerivedCategory.Q`. -/
def leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat
    (Q : CochainComplex C ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (Q.X i))] :
    DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q) ≅
      (MonoidalCategory.curriedTensor (CochainComplex C ℤ)).flip.obj Q ⋙
        DerivedCategory.Q := by
  have : Q.IsKFlat := Q.isKFlat_of_boundedAbove_flat b
  exact asIso (Functor.bifunctorCounit₂ α Q)

/-- The forward natural transformation of `leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat` is
`Functor.bifunctorCounit₂ α Q`. -/
@[simp]
theorem leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat_hom
    (Q : CochainComplex C ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (Q.X i))] :
    (leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat LF α Q b).hom =
      Functor.bifunctorCounit₂ α Q := by
  have : Q.IsKFlat := Q.isKFlat_of_boundedAbove_flat b
  simp [leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat]

end BoundedAboveFlat

end ModelComparison

section Unit

variable (C) [HasDerivedCategory.{w} C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]

/-- The left unitor of cochain complexes, followed by `DerivedCategory.Q`. -/
private def leftUnitorCompQ :
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj (𝟙_ (CochainComplex C ℤ)) ⋙
      DerivedCategory.Q ≅ DerivedCategory.Q :=
  Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso (CochainComplex C ℤ))
    DerivedCategory.Q ≪≫ DerivedCategory.Q.leftUnitor

/-- The right unitor of cochain complexes, followed by `DerivedCategory.Q`. -/
private def rightUnitorCompQ :
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ)).flip.obj (𝟙_ (CochainComplex C ℤ)) ⋙
      DerivedCategory.Q ≅ DerivedCategory.Q :=
  Functor.isoWhiskerRight (MonoidalCategory.rightUnitorNatIso (CochainComplex C ℤ))
    DerivedCategory.Q ≪≫ DerivedCategory.Q.leftUnitor

/-- The derived tensor product with the unit `𝟙_ C` placed in degree `0` on the left is naturally
isomorphic to the identity of the derived category. -/
def derivedTensorLeftUnitor :
    (derivedTensor C).obj ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≅ 𝟭 _ :=
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj (𝟙_ (CochainComplex C ℤ)) ⋙
        DerivedCategory.Q)
      ((derivedTensor C).obj ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))) :=
    ⟨asIso (Functor.bifunctorCounit₁ (derivedTensorCounit C) (𝟙_ (CochainComplex C ℤ)))⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ)) _
    DerivedCategory.Q _ (𝟭 _) (leftUnitorCompQ C)

/-- On a complex model `L`, the derived left unitor is the derived tensor comparison followed by
the left unitor of cochain complexes. -/
@[simp]
theorem derivedTensorLeftUnitor_hom_app_Q (L : CochainComplex C ℤ) :
    (derivedTensorLeftUnitor C).hom.app (DerivedCategory.Q.obj L) =
      ((derivedTensorCounit C).app (𝟙_ (CochainComplex C ℤ))).app L ≫
        DerivedCategory.Q.map (λ_ L).hom := by
  simp [derivedTensorLeftUnitor, Localization.liftNatIso, leftUnitorCompQ]

/-- The derived tensor product with the unit `𝟙_ C` placed in degree `0` on the right is naturally
isomorphic to the identity of the derived category. -/
def derivedTensorRightUnitor :
    (derivedTensor C).flip.obj ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≅ 𝟭 _ :=
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).flip.obj
        (𝟙_ (CochainComplex C ℤ)) ⋙ DerivedCategory.Q)
      ((derivedTensor C).flip.obj ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))) :=
    ⟨asIso (Functor.bifunctorCounit₂ (derivedTensorCounit C) (𝟙_ (CochainComplex C ℤ)))⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ)) _
    DerivedCategory.Q _ (𝟭 _) (rightUnitorCompQ C)

/-- On a complex model `K`, the derived right unitor is the derived tensor comparison followed by
the right unitor of cochain complexes. -/
@[simp]
theorem derivedTensorRightUnitor_hom_app_Q (K : CochainComplex C ℤ) :
    (derivedTensorRightUnitor C).hom.app (DerivedCategory.Q.obj K) =
      ((derivedTensorCounit C).app K).app (𝟙_ (CochainComplex C ℤ)) ≫
        DerivedCategory.Q.map (ρ_ K).hom := by
  simp [derivedTensorRightUnitor, Localization.liftNatIso, rightUnitorCompQ]

end Unit

end TauCeti
