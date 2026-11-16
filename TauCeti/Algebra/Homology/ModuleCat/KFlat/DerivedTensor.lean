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
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# The derived tensor product of unbounded complexes of modules

Taking the external product of the K-flat left derivability structure on
`CochainComplex (ModuleCat.{u} R) ℤ`
(`TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure`) with itself shows that the
totalized tensor product bifunctor on `CochainComplex (ModuleCat.{u} R) ℤ`, followed by the
localization functor `DerivedCategory.Q` to the unbounded derived category, admits a left derived
bifunctor (`TauCeti.ModuleCat.hasLeftDerivedFunctor₂_tensor`). This yields a canonical choice
`TauCeti.ModuleCat.derivedTensor R` (`- ⊗^L_R -`), while all model-comparison and unit properties
are proved universally for an arbitrary left derived bifunctor `(LT, α)` of tensoring:

* When `K` is K-flat (for instance when `K` is bounded above with flat terms,
  `CochainComplex.isKFlat_of_boundedAbove_flat`), `(α.app K).app L` is an isomorphism for every
  unbounded complex `L`, so `Functor.bifunctorCounit₁ α K` is a natural isomorphism and
  `LT.obj (DerivedCategory.Q.obj K)` is naturally isomorphic to `K.kFlatTensor`.
* Symmetrically, when `L` is K-flat (for instance when `L` is bounded above with flat terms),
  `(α.app K).app L` is an isomorphism for every unbounded complex `K`, so
  `Functor.bifunctorCounit₂ α L` is a natural isomorphism.
* Tensoring on the left or right with the monoidal unit complex `𝟙_` (`R` in degree `0`) is
  naturally isomorphic to the identity endofunctor of `DerivedCategory (ModuleCat.{u} R)`.

## Main definitions

* `TauCeti.ModuleCat.derivedTensor`: a left derived bifunctor `- ⊗^L_R -` on the unbounded derived
  category `DerivedCategory (ModuleCat.{u} R)`, with counit `TauCeti.ModuleCat.derivedTensorCounit`.
* `TauCeti.ModuleCat.derivedTensorObjIsoKFlatTensor`: comparison `LT.obj (Q.obj K) ≅ K.kFlatTensor`
  for any K-flat complex `K` and any left derived tensor bifunctor `(LT, α)`.
* `TauCeti.ModuleCat.derivedTensorLeftUnitor`, `TauCeti.ModuleCat.derivedTensorRightUnitor`: left
  and right unit natural isomorphisms on `DerivedCategory (ModuleCat.{u} R)`.

## Main results

* `TauCeti.ModuleCat.hasLeftDerivedFunctor₂_tensor`: the unbounded tensor product of module
  complexes admits a left derived bifunctor.
* `TauCeti.ModuleCat.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left` and
  `TauCeti.ModuleCat.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right`: one-sided
  K-flat complexes compute the derived tensor product against arbitrary unbounded complexes.
* `TauCeti.ModuleCat.isIso_bifunctorCounit₁_tensor_of_boundedAbove_flat` and
  `TauCeti.ModuleCat.isIso_bifunctorCounit₂_tensor_of_boundedAbove_flat`: bounded-above flat
  complexes compute the derived tensor product on either side.

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 06Y0, 06Y4, 064L, and 064M.
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
* [Joël Riou, *Formalization of derived categories in {Lean}/mathlib*][riou-2025]
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
  CochainComplex

universe u w

namespace TauCeti.ModuleCat

section DerivedTensor

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (_root_.ModuleCat.{u} R)]

variable (R) in
/-- Totalized tensor product on `CochainComplex (ModuleCat.{u} R) ℤ` followed by localization to
`DerivedCategory (ModuleCat.{u} R)` in the second variable. -/
abbrev tensorCompQ :
    CochainComplex (_root_.ModuleCat.{u} R) ℤ ⥤ CochainComplex (_root_.ModuleCat.{u} R) ℤ ⥤
      DerivedCategory (_root_.ModuleCat.{u} R) :=
  MonoidalCategory.curriedTensor (CochainComplex (_root_.ModuleCat.{u} R) ℤ) ⋙
    (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := _root_.ModuleCat.{u} R))

variable (R) in
/-- The product K-flat localizer morphism derives the uncurried total tensor product of module
complexes. -/
theorem derives_uncurry_tensorCompQ :
    ((kFlatLocalizerMorphism (_root_.ModuleCat.{u} R)).prod
      (kFlatLocalizerMorphism (_root_.ModuleCat.{u} R))).Derives
      (Functor.uncurry.obj (tensorCompQ R)) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁.hom := by simpa [mem_quasiIso_iff] using hf₁
  have : QuasiIso f₂.hom := by simpa [mem_quasiIso_iff] using hf₂
  have hmap : (((kFlatLocalizerMorphism (_root_.ModuleCat.{u} R)).prod
        (kFlatLocalizerMorphism (_root_.ModuleCat.{u} R))).functor ⋙
        Functor.uncurry.obj (tensorCompQ R)).map (f₁, f₂) =
      DerivedCategory.Q.map (HomologicalComplex.tensorHom f₁.hom f₂.hom) := by
    dsimp [tensorCompQ, kFlatLocalizerMorphism]
    rw [← Functor.map_comp, whiskerRight_eq_mapBifunctorMap, whiskerLeft_eq_mapBifunctorMap,
      ← mapBifunctorMap_comp, Category.comp_id, Category.id_comp]
  rw [hmap]
  infer_instance

variable (R) in
/-- **Existence of the derived tensor product.** For a commutative ring `R`, the totalized tensor
product on `CochainComplex (ModuleCat.{u} R) ℤ` followed by localization to
`DerivedCategory (ModuleCat.{u} R)` admits a left derived bifunctor with respect to
quasi-isomorphisms in both variables. -/
instance hasLeftDerivedFunctor₂_tensor :
    (MonoidalCategory.curriedTensor (CochainComplex (_root_.ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := _root_.ModuleCat.{u} R))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso (_root_.ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have := (derives_uncurry_tensorCompQ R).hasPointwiseLeftDerivedFunctor
  exact Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

section ModelComparison

variable {LT : DerivedCategory (_root_.ModuleCat.{u} R) ⥤ DerivedCategory (_root_.ModuleCat.{u} R) ⥤
    DerivedCategory (_root_.ModuleCat.{u} R)}
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj LT ⟶
    tensorCompQ R)
  [LT.IsLeftDerivedFunctor₂ α
    (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ)) (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ))]

/-- On a pair of K-flat complexes, the counit of any left derived tensor bifunctor is an
isomorphism. -/
private lemma isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat
    (K L : CochainComplex (_root_.ModuleCat.{u} R) ℤ) [K.IsKFlat] [L.IsKFlat] :
    IsIso ((α.app K).app L) :=
  (derives_uncurry_tensorCompQ R).isIso' (Functor.whiskeringLeft₂HomEquiv α)
    (⟨K, ‹_›⟩, ⟨L, ‹_›⟩)

/-- **Left K-flat model comparison.** When `K` is K-flat, `(α.app K).app L` is an isomorphism for
every (possibly unbounded and non-K-flat) cochain complex `L` of `R`-modules. -/
instance isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left
    (K L : CochainComplex (_root_.ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    IsIso ((α.app K).app L) := by
  obtain ⟨P, π, hπ, hP⟩ := L.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso π := hπ
  have : P.IsKFlat := hP
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
    (K : CochainComplex (_root_.ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    IsIso (Functor.bifunctorCounit₁ α K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro L
  dsimp only [Functor.bifunctorCounit₁_app]
  infer_instance

/-- **Right K-flat model comparison.** When `L` is K-flat, `(α.app K).app L` is an isomorphism for
every (possibly unbounded and non-K-flat) cochain complex `K` of `R`-modules. -/
instance isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right
    (K L : CochainComplex (_root_.ModuleCat.{u} R) ℤ) [L.IsKFlat] :
    IsIso ((α.app K).app L) := by
  obtain ⟨P, π, hπ, hP⟩ := K.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso π := hπ
  have : P.IsKFlat := hP
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
    (L : CochainComplex (_root_.ModuleCat.{u} R) ℤ) [L.IsKFlat] :
    IsIso (Functor.bifunctorCounit₂ α L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  dsimp only [Functor.bifunctorCounit₂_app]
  infer_instance

include α in
/-- When `K` is bounded above with flat terms, `Functor.bifunctorCounit₁ α K` is a natural
isomorphism. -/
theorem isIso_bifunctorCounit₁_tensor_of_boundedAbove_flat
    (K : CochainComplex (_root_.ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] :
    IsIso (Functor.bifunctorCounit₁ α K) :=
  have := K.isKFlat_of_boundedAbove_flat b
  inferInstance

include α in
/-- When `L` is bounded above with flat terms, `Functor.bifunctorCounit₂ α L` is a natural
isomorphism. -/
theorem isIso_bifunctorCounit₂_tensor_of_boundedAbove_flat
    (L : CochainComplex (_root_.ModuleCat.{u} R) ℤ) (b : ℤ)
    [L.IsStrictlyLE b] [∀ i, Module.Flat R (L.X i)] :
    IsIso (Functor.bifunctorCounit₂ α L) :=
  have := L.isKFlat_of_boundedAbove_flat b
  inferInstance

end ModelComparison

end DerivedTensor

section CanonicalAndUniversal

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (_root_.ModuleCat.{u} R)]

/-- The canonical left derived tensor bifunctor `- ⊗^L_R -` on the unbounded derived category
`DerivedCategory (ModuleCat.{u} R)`. -/
def derivedTensor :
    DerivedCategory (_root_.ModuleCat.{u} R) ⥤ DerivedCategory (_root_.ModuleCat.{u} R) ⥤
      DerivedCategory (_root_.ModuleCat.{u} R) :=
  Functor.leftDerived₂ (tensorCompQ R) DerivedCategory.Q DerivedCategory.Q
    (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ)) (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ))

/-- The universal counit natural transformation exhibiting `TauCeti.ModuleCat.derivedTensor R` as a
left derived bifunctor of totalized tensoring of cochain complexes. -/
def derivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj
      (derivedTensor R) ⟶ tensorCompQ R :=
  Functor.leftDerivedCounit₂ (tensorCompQ R) DerivedCategory.Q DerivedCategory.Q
    (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ)) (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ))

instance isLeftDerivedFunctor₂_derivedTensor :
    (derivedTensor R).IsLeftDerivedFunctor₂ (derivedTensorCounit R)
      (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ)) (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ)) := by
  dsimp [derivedTensor, derivedTensorCounit]
  infer_instance

section UniversalProperties

variable {R}
variable {LT : DerivedCategory (_root_.ModuleCat.{u} R) ⥤ DerivedCategory (_root_.ModuleCat.{u} R) ⥤
    DerivedCategory (_root_.ModuleCat.{u} R)}
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj LT ⟶
    tensorCompQ R)
  [LT.IsLeftDerivedFunctor₂ α
    (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ)) (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ))]

@[simps!]
private def tensorCompQObjIsoMap₂CochainComplex (K : CochainComplex (_root_.ModuleCat.{u} R) ℤ) :
    (tensorCompQ R).obj K ≅
      ((MonoidalCategory.curriedTensor (_root_.ModuleCat.{u} R)).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q :=
  NatIso.ofComponents (fun L ↦ Iso.refl (DerivedCategory.Q.obj (K ⊗ L))) fun f ↦ by
    dsimp [tensorCompQ]
    rw [Category.id_comp, Category.comp_id, whiskerLeft_eq_mapBifunctorMap]

include α

/-- For any K-flat complex `K` and any left derived tensor bifunctor `(LT, α)`, evaluating `LT` at
`DerivedCategory.Q.obj K` is naturally isomorphic to `K.kFlatTensor`. -/
def derivedTensorObjIsoKFlatTensor (K : CochainComplex (_root_.ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    LT.obj (DerivedCategory.Q.obj K) ≅ K.kFlatTensor :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ))
    (DerivedCategory.Q ⋙ LT.obj (DerivedCategory.Q.obj K))
    (((MonoidalCategory.curriedTensor (_root_.ModuleCat.{u} R)).map₂CochainComplex.obj K) ⋙
      DerivedCategory.Q)
    (LT.obj (DerivedCategory.Q.obj K)) K.kFlatTensor
    (asIso (Functor.bifunctorCounit₁ α K) ≪≫ tensorCompQObjIsoMap₂CochainComplex K)

/-- On complex models, `derivedTensorObjIsoKFlatTensor` intertwines `kFlatTensorModelIso` with the
counit `α` of the left derived tensor bifunctor. -/
@[reassoc (attr := simp)]
lemma derivedTensorObjIsoKFlatTensor_hom_app_Q
    (K L : CochainComplex (_root_.ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    (derivedTensorObjIsoKFlatTensor α K).hom.app (DerivedCategory.Q.obj L) ≫
      K.kFlatTensorModelIso.hom.app L = (α.app K).app L := by
  rw [derivedTensorObjIsoKFlatTensor, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    kFlatTensorModelIso_eq_liftingIso, Category.assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  simp [tensorCompQ]

/-- Left unit natural isomorphism `R[0] ⊗^L M ≅ M` for any left derived tensor bifunctor `(LT, α)`
on `DerivedCategory (ModuleCat.{u} R)`. -/
def derivedTensorLeftUnitor :
    LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))) ≅
      𝟭 (DerivedCategory (_root_.ModuleCat.{u} R)) :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ))
    (DerivedCategory.Q ⋙
      LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (_root_.ModuleCat.{u} R)))
    (LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))))
    (𝟭 (DerivedCategory (_root_.ModuleCat.{u} R)))
    (asIso (Functor.bifunctorCounit₁ α (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `derivedTensorLeftUnitor` is the derived-tensor counit followed by the
monoidal left unitor of `CochainComplex (ModuleCat.{u} R) ℤ`. -/
@[simp]
lemma derivedTensorLeftUnitor_hom_app_Q (L : CochainComplex (_root_.ModuleCat.{u} R) ℤ) :
    (derivedTensorLeftUnitor α).hom.app (DerivedCategory.Q.obj L) =
      (α.app (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))).app L ≫
        DerivedCategory.Q.map (λ_ L).hom := by
  simp [derivedTensorLeftUnitor]

/-- Right unit natural isomorphism `M ⊗^L R[0] ≅ M` for any left derived tensor bifunctor `(LT, α)`
on `DerivedCategory (ModuleCat.{u} R)`. -/
def derivedTensorRightUnitor :
    LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))) ≅
      𝟭 (DerivedCategory (_root_.ModuleCat.{u} R)) :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso (_root_.ModuleCat.{u} R) (.up ℤ))
    (DerivedCategory.Q ⋙
      LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (_root_.ModuleCat.{u} R)))
    (LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))))
    (𝟭 (DerivedCategory (_root_.ModuleCat.{u} R)))
    (asIso (Functor.bifunctorCounit₂ α (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.rightUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `derivedTensorRightUnitor` is the derived-tensor counit followed by the
monoidal right unitor of `CochainComplex (ModuleCat.{u} R) ℤ`. -/
@[simp]
lemma derivedTensorRightUnitor_hom_app_Q (K : CochainComplex (_root_.ModuleCat.{u} R) ℤ) :
    (derivedTensorRightUnitor α).hom.app (DerivedCategory.Q.obj K) =
      (α.app K).app (𝟙_ (CochainComplex (_root_.ModuleCat.{u} R) ℤ)) ≫
        DerivedCategory.Q.map (ρ_ K).hom := by
  simp [derivedTensorRightUnitor]

end UniversalProperties

end CanonicalAndUniversal

end TauCeti.ModuleCat
