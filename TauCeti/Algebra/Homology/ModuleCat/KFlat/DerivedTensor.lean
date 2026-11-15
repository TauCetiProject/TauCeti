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
public import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import TauCeti.Algebra.Homology.Monoidal.Braiding

/-!
# The derived tensor product of unbounded complexes of modules

For a commutative ring `R`, the free–forgetful adjunction on `ModuleCat.{u} R` supplies a
functorial flat cover of every `R`-module. Consequently, the inclusion
`CochainComplex.kFlatLocalizerMorphism (ModuleCat.{u} R)` of K-flat complexes into all unbounded
cochain complexes of `R`-modules is a left derivability structure with respect to
quasi-isomorphisms, induces an equivalence on localized categories, and admits left resolutions of
arrows.

Taking the external product of this left derivability structure with itself shows that the
totalized tensor product bifunctor on `CochainComplex (ModuleCat.{u} R) ℤ`, followed by the
localization functor `DerivedCategory.Q` to the unbounded derived category, admits a left derived
bifunctor (`CochainComplex.hasLeftDerivedFunctor₂_tensor`). This yields a canonical choice
`DerivedCategory.derivedTensor R` (`- ⊗^L_R -`), while all model-comparison and unit properties are
proved universally for an arbitrary left derived bifunctor `(LT, α)` of tensoring:

* When `K` is K-flat (for instance when `K` is bounded above with flat terms,
  `CochainComplex.isKFlat_of_moduleCat_boundedAbove_flat`), `(α.app K).app L` is an isomorphism for
  every unbounded complex `L`, so `Functor.bifunctorCounit₁ α K` is a natural isomorphism and
  `LT.obj (DerivedCategory.Q.obj K)` is naturally isomorphic to `K.kFlatTensor`.
* Symmetrically, when `L` is K-flat, `(α.app K).app L` is an isomorphism for every unbounded
  complex `K`, so `Functor.bifunctorCounit₂ α L` is a natural isomorphism.
* Tensoring on the left or right with the monoidal unit complex `𝟙_` (`R` in degree `0`) is
  naturally isomorphic to the identity endofunctor of `DerivedCategory (ModuleCat.{u} R)`.

## Main definitions

* `DerivedCategory.derivedTensor`: a left derived bifunctor `- ⊗^L_R -` on the unbounded derived
  category `DerivedCategory (ModuleCat.{u} R)`, with counit `DerivedCategory.derivedTensorCounit`.
* `DerivedCategory.derivedTensorObjIsoKFlatTensor`: comparison `LT.obj (Q.obj K) ≅ K.kFlatTensor`
  for any K-flat complex `K` and any left derived tensor bifunctor `(LT, α)`.
* `DerivedCategory.derivedTensorLeftUnitor`, `DerivedCategory.derivedTensorRightUnitor`: left and
  right unit natural isomorphisms on `DerivedCategory (ModuleCat.{u} R)`.

## Main results

* `CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat`: K-flat complexes
  of `R`-modules form a left derivability structure.
* `CochainComplex.hasLeftDerivedFunctor₂_tensor`: the unbounded tensor product of module complexes
  admits a left derived bifunctor.
* `CochainComplex.isIso_app_app_of_isLeftDerivedFunctor₂_of_isKFlat_left` and
  `CochainComplex.isIso_app_app_of_isLeftDerivedFunctor₂_of_isKFlat_right`: one-sided K-flat
  complexes compute the derived tensor product against arbitrary unbounded complexes.

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 06Y0, 06Y4, 064L, and 064M.
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
* [Joël Riou, *Formalization of derived categories in {Lean}/mathlib*][riou-2025]
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

universe u w

namespace ModuleCat

section FreeCover

variable (R : Type u) [CommRing R]

/-- The functorial free cover `M ↦ (M →₀ R)` on `ModuleCat.{u} R`. -/
def freeCoverFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R

/-- The canonical epimorphic natural transformation `(M →₀ R) ⟶ M` on `ModuleCat.{u} R`, defined as
the counit of `ModuleCat.adj R`. -/
def freeCoverπ : freeCoverFunctor R ⟶ 𝟭 (ModuleCat.{u} R) :=
  (ModuleCat.adj R).counit

instance epi_freeCoverπ_app (M : ModuleCat.{u} R) : Epi ((freeCoverπ R).app M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro m
  refine ⟨ModuleCat.freeMk m, ?_⟩
  -- Unfold `(ModuleCat.adj R).counit.app M` and `ConcreteCategory.hom` to `ModuleCat.freeDesc`.
  change (ModuleCat.freeDesc (𝟙 _)) (ModuleCat.freeMk m) = m
  simp

instance flat_freeCoverFunctor_obj (M : ModuleCat.{u} R) :
    Module.Flat R ((freeCoverFunctor R).obj M) :=
  Module.Flat.finsupp M

end FreeCover

end ModuleCat

namespace CochainComplex

variable {R : Type u} [CommRing R]

section DerivabilityStructure

instance hasLeftResolutions_arrow_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).arrow.HasLeftResolutions := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  exact hasLeftResolutions_arrow_kFlatLocalizerMorphism
    (ModuleCat.freeCoverFunctor R) (ModuleCat.freeCoverπ R)

instance isLocalizedEquivalence_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLocalizedEquivalence := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  exact isLocalizedEquivalence_kFlatLocalizerMorphism
    (ModuleCat.freeCoverFunctor R) (ModuleCat.freeCoverπ R)

/-- The inclusion of K-flat complexes into `CochainComplex (ModuleCat.{u} R) ℤ` is a left
derivability structure with respect to quasi-isomorphisms. -/
instance isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLeftDerivabilityStructure := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  exact isLeftDerivabilityStructure_kFlatLocalizerMorphism
    (ModuleCat.freeCoverFunctor R) (ModuleCat.freeCoverπ R)

/-- A bounded-above cochain complex of flat `R`-modules is K-flat. -/
theorem isKFlat_of_moduleCat_boundedAbove_flat (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] : K.IsKFlat := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  exact K.isKFlat_of_boundedAbove_flat b

/-- The monoidal unit cochain complex `R[0]` in `CochainComplex (ModuleCat.{u} R) ℤ` is K-flat. -/
instance isKFlat_tensorUnit_moduleCat :
    (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).IsKFlat :=
  isKFlat_single_of_flat (𝟙_ (ModuleCat.{u} R)) 0

end DerivabilityStructure

section QuasiIso

/-- A quasi-isomorphism between K-flat complexes of `R`-modules remains a quasi-isomorphism after
tensoring on the left with an arbitrary, possibly unbounded, complex `A`. -/
instance quasiIso_id_tensorHom_of_isKFlat (A : CochainComplex (ModuleCat.{u} R) ℤ)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 A) f) := by
  rw [HomologicalComplex.tensorHom, ← whiskerLeft_eq_mapBifunctorMap]
  have : QuasiIso (f ▷ A) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (HomologicalComplex.tensorHom f (𝟙 A)))
  exact quasiIso_of_arrow_mk_iso (f ▷ A) (A ◁ f)
    (Arrow.isoMk (β_ K A) (β_ L A) (BraidedCategory.braiding_naturality_left f A).symm)

/-- The tensor product of two quasi-isomorphisms between K-flat complexes of `R`-modules is a
quasi-isomorphism. -/
instance quasiIso_tensorHom_of_isKFlat
    {K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    [K₁.IsKFlat] [L₁.IsKFlat] [K₂.IsKFlat] [L₂.IsKFlat]
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [QuasiIso f] [QuasiIso g] :
    QuasiIso (HomologicalComplex.tensorHom f g) := by
  have hfg : HomologicalComplex.tensorHom f g =
      HomologicalComplex.tensorHom f (𝟙 K₂) ≫ HomologicalComplex.tensorHom (𝟙 L₁) g := by
    simp only [← mapBifunctorMap_comp, Category.id_comp, Category.comp_id]
  rw [hfg]
  infer_instance

end QuasiIso

section DerivedTensor

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

variable (R) in
/-- Totalized tensor product on `CochainComplex (ModuleCat.{u} R) ℤ` followed by localization to
`DerivedCategory (ModuleCat.{u} R)` in the second variable. -/
abbrev tensorCompQ :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
    (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R))

variable (R) in
/-- The product K-flat localizer morphism derives the uncurried total tensor product of module
complexes. -/
theorem derives_uncurry_tensorCompQ :
    ((kFlatLocalizerMorphism (ModuleCat.{u} R)).prod
      (kFlatLocalizerMorphism (ModuleCat.{u} R))).Derives
      (Functor.uncurry.obj (tensorCompQ R)) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁.hom := by simpa [mem_quasiIso_iff] using hf₁
  have : QuasiIso f₂.hom := by simpa [mem_quasiIso_iff] using hf₂
  have hmap : (((kFlatLocalizerMorphism (ModuleCat.{u} R)).prod
        (kFlatLocalizerMorphism (ModuleCat.{u} R))).functor ⋙
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
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := ModuleCat.{u} R))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have := (derives_uncurry_tensorCompQ R).hasPointwiseLeftDerivedFunctor
  exact Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

section ModelComparison

variable {LT : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R)}
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj LT ⟶
    tensorCompQ R)
  [LT.IsLeftDerivedFunctor₂ α
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]

/-- On a pair of K-flat complexes, the counit of any left derived tensor bifunctor is an
isomorphism. -/
instance isIso_app_app_of_isLeftDerivedFunctor₂_of_isKFlat
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] [L.IsKFlat] :
    IsIso ((α.app K).app L) :=
  (derives_uncurry_tensorCompQ R).isIso' (Functor.whiskeringLeft₂HomEquiv α)
    (⟨K, ‹_›⟩, ⟨L, ‹_›⟩)

/-- **Left K-flat model comparison.** When `K` is K-flat, `(α.app K).app L` is an isomorphism for
every (possibly unbounded and non-K-flat) cochain complex `L` of `R`-modules. -/
instance isIso_app_app_of_isLeftDerivedFunctor₂_of_isKFlat_left
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    IsIso ((α.app K).app L) := by
  obtain ⟨P, π, hπ, hP⟩ := L.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso π := hπ
  have : P.IsKFlat := hP
  have hnat := (α.app K).naturality π
  dsimp [tensorCompQ] at hnat
  have : IsIso (DerivedCategory.Q.map (K ◁ π)) := by
    rw [whiskerLeft_eq_mapBifunctorMap]
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (HomologicalComplex.tensorHom (𝟙 K) π)))
  rw [← isIso_comp_left_iff ((LT.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map π)),
    hnat]
  infer_instance

/-- When `K` is K-flat, `Functor.bifunctorCounit₁ α K` is a natural isomorphism. -/
instance isIso_bifunctorCounit₁_of_isKFlat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    IsIso (Functor.bifunctorCounit₁ α K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro L
  dsimp only [Functor.bifunctorCounit₁_app]
  infer_instance

/-- **Right K-flat model comparison.** When `L` is K-flat, `(α.app K).app L` is an isomorphism for
every (possibly unbounded and non-K-flat) cochain complex `K` of `R`-modules. -/
instance isIso_app_app_of_isLeftDerivedFunctor₂_of_isKFlat_right
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [L.IsKFlat] :
    IsIso ((α.app K).app L) := by
  obtain ⟨P, π, hπ, hP⟩ := K.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso π := hπ
  have : P.IsKFlat := hP
  have hnat := NatTrans.congr_app (α.naturality π) L
  dsimp [tensorCompQ] at hnat
  have : IsIso (DerivedCategory.Q.map (π ▷ L)) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (HomologicalComplex.tensorHom π (𝟙 L))))
  rw [← isIso_comp_left_iff (((LT.map (DerivedCategory.Q.map π)).app (DerivedCategory.Q.obj L))),
    hnat]
  infer_instance

/-- When `L` is K-flat, `Functor.bifunctorCounit₂ α L` is a natural isomorphism. -/
instance isIso_bifunctorCounit₂_of_isKFlat
    (L : CochainComplex (ModuleCat.{u} R) ℤ) [L.IsKFlat] :
    IsIso (Functor.bifunctorCounit₂ α L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  dsimp only [Functor.bifunctorCounit₂_app]
  infer_instance

/-- When `K` is bounded above with flat terms, `Functor.bifunctorCounit₁ α K` is a natural
isomorphism. -/
theorem isIso_bifunctorCounit₁_of_boundedAbove_flat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] :
    IsIso (Functor.bifunctorCounit₁ α K) :=
  have := K.isKFlat_of_moduleCat_boundedAbove_flat b
  inferInstance

end ModelComparison

end DerivedTensor

end CochainComplex

namespace DerivedCategory

open CochainComplex

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The canonical left derived tensor bifunctor `- ⊗^L_R -` on the unbounded derived category
`DerivedCategory (ModuleCat.{u} R)`. -/
def derivedTensor :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  Functor.leftDerived₂ (tensorCompQ R) DerivedCategory.Q DerivedCategory.Q
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))

/-- The universal counit natural transformation exhibiting `DerivedCategory.derivedTensor R` as a
left derived bifunctor of totalized tensoring of cochain complexes. -/
def derivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj
      (derivedTensor R) ⟶ tensorCompQ R :=
  Functor.leftDerivedCounit₂ (tensorCompQ R) DerivedCategory.Q DerivedCategory.Q
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))

instance isLeftDerivedFunctor₂_derivedTensor :
    (derivedTensor R).IsLeftDerivedFunctor₂ (derivedTensorCounit R)
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  dsimp [derivedTensor, derivedTensorCounit]
  infer_instance

section UniversalProperties

variable {R}
variable {LT : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R)}
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj LT ⟶
    tensorCompQ R)
  [LT.IsLeftDerivedFunctor₂ α
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]

private def tensorCompQObjIsoMap₂CochainComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorCompQ R).obj K ≅
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q :=
  NatIso.ofComponents (fun L ↦ Iso.refl (DerivedCategory.Q.obj (K ⊗ L))) fun f ↦ by
    dsimp [tensorCompQ]
    rw [Category.id_comp, Category.comp_id, whiskerLeft_eq_mapBifunctorMap]

include α

/-- For any K-flat complex `K` and any left derived tensor bifunctor `(LT, α)`, evaluating `LT` at
`DerivedCategory.Q.obj K` is naturally isomorphic to `K.kFlatTensor`. -/
def derivedTensorObjIsoKFlatTensor (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    LT.obj (DerivedCategory.Q.obj K) ≅ K.kFlatTensor :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
    (DerivedCategory.Q ⋙ LT.obj (DerivedCategory.Q.obj K))
    (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K) ⋙
      DerivedCategory.Q)
    (LT.obj (DerivedCategory.Q.obj K)) K.kFlatTensor
    (asIso (Functor.bifunctorCounit₁ α K) ≪≫ tensorCompQObjIsoMap₂CochainComplex K)

/-- On complex models, `derivedTensorObjIsoKFlatTensor` intertwines `kFlatTensorModelIso` with the
counit `α` of the left derived tensor bifunctor. -/
@[reassoc (attr := simp)]
lemma derivedTensorObjIsoKFlatTensor_hom_app_Q
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    (derivedTensorObjIsoKFlatTensor α K).hom.app (DerivedCategory.Q.obj L) ≫
      K.kFlatTensorModelIso.hom.app L = (α.app K).app L := by
  dsimp only [derivedTensorObjIsoKFlatTensor]
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    kFlatTensorModelIso_eq_liftingIso, Category.assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  simp only [Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.trans_hom, NatTrans.comp_app,
    NatTrans.id_app, asIso_hom, Functor.bifunctorCounit₁_app]
  let f : (LT.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj (K ⊗ L) := (α.app K).app L
  exact (Category.id_comp _).trans (Category.comp_id f)

/-- Left unit natural isomorphism `R[0] ⊗^L M ≅ M` for any left derived tensor bifunctor `(LT, α)`
on `DerivedCategory (ModuleCat.{u} R)`. -/
def derivedTensorLeftUnitor :
    LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} R)) :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
    (DerivedCategory.Q ⋙
      LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} R)))
    (LT.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))))
    (𝟭 (DerivedCategory (ModuleCat.{u} R)))
    (asIso (Functor.bifunctorCounit₁ α (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `derivedTensorLeftUnitor` is the derived-tensor counit followed by the
monoidal left unitor of `CochainComplex (ModuleCat.{u} R) ℤ`. -/
@[simp]
lemma derivedTensorLeftUnitor_hom_app_Q (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedTensorLeftUnitor α).hom.app (DerivedCategory.Q.obj L) =
      (α.app (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).app L ≫
        DerivedCategory.Q.map (λ_ L).hom := by
  simp [derivedTensorLeftUnitor]

/-- Right unit natural isomorphism `M ⊗^L R[0] ≅ M` for any left derived tensor bifunctor `(LT, α)`
on `DerivedCategory (ModuleCat.{u} R)`. -/
def derivedTensorRightUnitor :
    LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} R)) :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
    (DerivedCategory.Q ⋙
      LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} R)))
    (LT.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))))
    (𝟭 (DerivedCategory (ModuleCat.{u} R)))
    (asIso (Functor.bifunctorCounit₂ α (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.rightUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `derivedTensorRightUnitor` is the derived-tensor counit followed by the
monoidal right unitor of `CochainComplex (ModuleCat.{u} R) ℤ`. -/
@[simp]
lemma derivedTensorRightUnitor_hom_app_Q (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedTensorRightUnitor α).hom.app (DerivedCategory.Q.obj K) =
      (α.app K).app (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ≫
        DerivedCategory.Q.map (ρ_ K).hom := by
  simp [derivedTensorRightUnitor]

end UniversalProperties

end DerivedCategory
