/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Tensor
public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Derived tensor products on unbounded derived categories of modules

For a commutative ring `R`, the free-forgetful comonad
`forget (ModuleCat.{u} R) ⋙ ModuleCat.free R` and its counit `(ModuleCat.adj R).counit` furnish a
functorial flat epimorphic cover of every `R`-module. Applying
`CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism` shows that the inclusion of
K-flat complexes of `R`-modules into `CochainComplex (ModuleCat.{u} R) ℤ` is a left derivability
structure for quasi-isomorphisms.

Combining this left derivability structure with the identity localizer morphism on the other
factor (`LocalizerMorphism.prod`), and using that tensoring with a K-flat complex preserves
quasi-isomorphisms while quasi-isomorphisms between K-flat complexes are preserved by tensoring
with any complex (`CochainComplex.quasiIso_id_tensorHom`,
`CochainComplex.quasiIso_tensorHom_id_of_isKFlat`), we prove that the total tensor product of
unbounded cochain complexes of `R`-modules admits a pointwise left derived bifunctor
(`CochainComplex.hasLeftDerivedFunctor₂_tensor`).

Using `LocalizerMorphism.Derives.isIso'` on both product derivability structures yields the
one-sided K-flat model theorem: for any left derived tensor bifunctor `T` with comparison `α`,
the map `(α.app K).app L : (T.obj (Q.obj K)).obj (Q.obj L) ⟶ Q.obj (K ⊗ L)` is an isomorphism
whenever either `K` or `L` is K-flat — in particular whenever either factor is a bounded-above
complex of flat modules. This identifies `T.obj (Q.obj K)` with `K.kFlatTensor`, identifies
tensoring on either side with the monoidal unit `R[0]` with the identity functor of `D(R)`, and
yields the involutive symmetry isomorphism `T.flip ≅ T` induced by the Koszul braiding.

## Main results

* `CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat`: the inclusion of
  K-flat complexes of `R`-modules is a left derivability structure for quasi-isomorphisms.
* `CochainComplex.hasLeftDerivedFunctor₂_tensor`: the tensor product of unbounded cochain
  complexes of `R`-modules admits a left derived bifunctor on `DerivedCategory (ModuleCat.{u} R)`.
* `CochainComplex.isIso_derivedTensorCounit_of_isKFlat_left` and
  `CochainComplex.isIso_derivedTensorCounit_of_isKFlat_right`: any left derived tensor bifunctor
  is computed by the ordinary total tensor product whenever either factor is K-flat.
* `CochainComplex.isIso_derivedTensorCounit_of_boundedAbove_flat_left` and
  `CochainComplex.isIso_derivedTensorCounit_of_boundedAbove_flat_right`: specialization to
  bounded-above complexes of flat modules.
* `CochainComplex.derivedTensorObjIsoKFlatTensor`: for K-flat `K`, fixing the left variable at
  `DerivedCategory.Q.obj K` recovers `K.kFlatTensor`.
* `CochainComplex.derivedTensorLeftUnitIso` and `CochainComplex.derivedTensorRightUnitIso`:
  derived tensoring with the monoidal unit `R[0]` on either side is naturally isomorphic to the
  identity functor of `DerivedCategory (ModuleCat.{u} R)`.
* `CochainComplex.derivedTensorFlipIso`: involutive symmetry `T.flip ≅ T` of any left derived
  tensor bifunctor.

## References

* The Stacks Project, More on Algebra, Section 15.60, Definition 15.60.13 and Lemmas 15.60.2,
  15.60.7, 15.60.10, 15.60.12 (Tags 064K, 064L, 064M, 06Y0, 06Y4).
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped MonoidalCategory

namespace CochainComplex

universe u w

variable {R : Type u} [CommRing R]

section DerivabilityStructure

/-- **The K-flat left derivability structure for complexes of modules.** The inclusion of the full
subcategory of K-flat complexes into `CochainComplex (ModuleCat.{u} R) ℤ` is a left derivability
structure with respect to quasi-isomorphisms. -/
instance isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLeftDerivabilityStructure := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have : ∀ X : ModuleCat.{u} R, Epi ((ModuleCat.adj R).counit.app X) :=
    fun X ↦ (ModuleCat.adj R).counit_epi_of_R_faithful X
  have : ∀ X : ModuleCat.{u} R,
      PreservesFiniteLimits (tensorLeft ((forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X)) :=
    fun X ↦ inferInstanceAs (PreservesFiniteLimits (tensorLeft (ModuleCat.of R (X →₀ R))))
  exact isLeftDerivabilityStructure_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

/-- Morphisms of cochain complexes of `R`-modules admit left resolutions by morphisms of K-flat
complexes. -/
instance hasLeftResolutions_arrow_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).arrow.HasLeftResolutions := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have : ∀ X : ModuleCat.{u} R, Epi ((ModuleCat.adj R).counit.app X) :=
    fun X ↦ (ModuleCat.adj R).counit_epi_of_R_faithful X
  have : ∀ X : ModuleCat.{u} R,
      PreservesFiniteLimits (tensorLeft ((forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X)) :=
    fun X ↦ inferInstanceAs (PreservesFiniteLimits (tensorLeft (ModuleCat.of R (X →₀ R))))
  exact hasLeftResolutions_arrow_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

/-- A bounded-above cochain complex of flat `R`-modules is K-flat. -/
theorem isKFlat_of_boundedAbove_flat_moduleCat (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) [K.IsStrictlyLE n] (hK : ∀ i, Module.Flat R (K.X i)) : K.IsKFlat := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have (i : ℤ) : PreservesFiniteLimits (tensorLeft (K.X i)) := by
    have := hK i
    infer_instance
  exact isKFlat_of_boundedAbove_flat K n

end DerivabilityStructure

section DerivedTensor

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The total tensor product of cochain complexes of `R`-modules followed by localization is
derived by the product of the K-flat left derivability structure on the left and the identity
localizer morphism on the right. -/
lemma derives_uncurry_tensor_left (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    ((kFlatLocalizerMorphism (ModuleCat.{u} R)).prod
      (LocalizerMorphism.id (quasiIso (ModuleCat.{u} R) (.up ℤ)))).Derives
      (Functor.uncurry.obj (curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (DerivedCategory.Q (C := ModuleCat.{u} R)))) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁.hom := (mem_quasiIso_iff _).1 hf₁
  have : QuasiIso f₂ := (mem_quasiIso_iff _).1 hf₂
  have h₁ : QuasiIso (f₁.hom ▷ K₂) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (HomologicalComplex.tensorHom f₁.hom (𝟙 K₂)))
  have h₂ : QuasiIso (L₁.obj ◁ f₂) := by
    rw [whiskerLeft_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (HomologicalComplex.tensorHom (𝟙 L₁.obj) f₂))
  have : IsIso (DerivedCategory.Q.map (f₁.hom ▷ K₂)) :=
    Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)) _
      ((mem_quasiIso_iff _).2 h₁)
  have : IsIso (DerivedCategory.Q.map (L₁.obj ◁ f₂)) :=
    Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)) _
      ((mem_quasiIso_iff _).2 h₂)
  dsimp [LocalizerMorphism.id]
  infer_instance

/-- Symmetrically, the total tensor product followed by localization is derived by the product of
the identity localizer morphism on the left and the K-flat left derivability structure on the
right. -/
lemma derives_uncurry_tensor_right (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    ((LocalizerMorphism.id (quasiIso (ModuleCat.{u} R) (.up ℤ))).prod
      (kFlatLocalizerMorphism (ModuleCat.{u} R))).Derives
      (Functor.uncurry.obj (curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (DerivedCategory.Q (C := ModuleCat.{u} R)))) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁ := (mem_quasiIso_iff _).1 hf₁
  have : QuasiIso f₂.hom := (mem_quasiIso_iff _).1 hf₂
  have h₁ : QuasiIso (f₁ ▷ K₂.obj) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (HomologicalComplex.tensorHom f₁ (𝟙 K₂.obj)))
  have h₂ : QuasiIso (L₁ ◁ f₂.hom) := by
    rw [whiskerLeft_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (HomologicalComplex.tensorHom (𝟙 L₁) f₂.hom))
  have : IsIso (DerivedCategory.Q.map (f₁ ▷ K₂.obj)) :=
    Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)) _
      ((mem_quasiIso_iff _).2 h₁)
  have : IsIso (DerivedCategory.Q.map (L₁ ◁ f₂.hom)) :=
    Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)) _
      ((mem_quasiIso_iff _).2 h₂)
  dsimp [LocalizerMorphism.id]
  infer_instance

/-- The uncurried tensor product of cochain complexes of `R`-modules admits a pointwise left
derived functor with respect to quasi-isomorphisms in both variables. -/
instance hasPointwiseLeftDerivedFunctor_uncurry_tensor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (Functor.uncurry.obj (curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := ModuleCat.{u} R)))).HasPointwiseLeftDerivedFunctor
      ((quasiIso (ModuleCat.{u} R) (.up ℤ)).prod (quasiIso (ModuleCat.{u} R) (.up ℤ))) :=
  (derives_uncurry_tensor_left R).hasPointwiseLeftDerivedFunctor

/-- **Existence of the derived tensor product.** For a commutative ring `R`, the total tensor
product of unbounded cochain complexes of `R`-modules followed by `DerivedCategory.Q` admits a
left derived bifunctor with respect to quasi-isomorphisms in both variables. -/
instance hasLeftDerivedFunctor₂_tensor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := ModuleCat.{u} R))).HasLeftDerivedFunctor₂
      (quasiIso (ModuleCat.{u} R) (.up ℤ))
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
  inferInstance

section ModelComparison

variable (T : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R))
  (α : (((Functor.whiskeringLeft₂ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R))).obj
    DerivedCategory.Q).obj T ⟶
    curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q)
  [T.IsLeftDerivedFunctor₂ α (quasiIso (ModuleCat.{u} R) (.up ℤ))
    (quasiIso (ModuleCat.{u} R) (.up ℤ))]

/-- **Left K-flat model computation for derived tensor products.** For any left derived tensor
bifunctor `T` with comparison `α`, the comparison `(α.app K).app L` is an isomorphism whenever
`K` is K-flat and `L` is an arbitrary complex. -/
instance isIso_derivedTensorCounit_of_isKFlat_left
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    IsIso ((α.app K).app L) :=
  (derives_uncurry_tensor_left R).isIso' (Functor.whiskeringLeft₂HomEquiv α)
    (⟨K, (isKFlatProperty_iff K).2 inferInstance⟩, L)

/-- **Right K-flat model computation for derived tensor products.** For any left derived tensor
bifunctor `T` with comparison `α`, the comparison `(α.app K).app L` is an isomorphism whenever
`L` is K-flat and `K` is an arbitrary complex. -/
instance isIso_derivedTensorCounit_of_isKFlat_right
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [L.IsKFlat] :
    IsIso ((α.app K).app L) :=
  (derives_uncurry_tensor_right R).isIso' (Functor.whiskeringLeft₂HomEquiv α)
    (K, ⟨L, (isKFlatProperty_iff L).2 inferInstance⟩)

/-- For a bounded-above complex `K` of flat `R`-modules and any complex `L`, the derived tensor
comparison `(α.app K).app L` is an isomorphism. -/
lemma isIso_derivedTensorCounit_of_boundedAbove_flat_left
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsStrictlyLE n]
    (hK : ∀ i, Module.Flat R (K.X i)) :
    IsIso ((α.app K).app L) :=
  have := isKFlat_of_boundedAbove_flat_moduleCat K n hK
  inferInstance

/-- For any complex `K` and a bounded-above complex `L` of flat `R`-modules, the derived tensor
comparison `(α.app K).app L` is an isomorphism. -/
lemma isIso_derivedTensorCounit_of_boundedAbove_flat_right
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [L.IsStrictlyLE n]
    (hL : ∀ i, Module.Flat R (L.X i)) :
    IsIso ((α.app K).app L) :=
  have := isKFlat_of_boundedAbove_flat_moduleCat L n hL
  inferInstance

/-- Fixing the left variable of a left derived tensor bifunctor `T` at the image of a K-flat
complex `K` recovers the localized tensor functor `K.kFlatTensor`. -/
def derivedTensorObjIsoKFlatTensor (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    T.obj (DerivedCategory.Q.obj K) ≅ K.kFlatTensor := by
  haveI : IsIso (Functor.bifunctorCounit₁ α K) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro L
    exact isIso_derivedTensorCounit_of_isKFlat_left T α K L
  let e : (curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).obj K ≅
      (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
      simp [whiskerLeft_eq_mapBifunctorMap]
  haveI : Localization.Lifting DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
      ((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K ⋙ DerivedCategory.Q)
      (T.obj (DerivedCategory.Q.obj K)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α K) ≪≫ Functor.isoWhiskerRight e DerivedCategory.Q⟩
  exact Localization.liftNatIso DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
    ((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K ⋙ DerivedCategory.Q)
    ((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K ⋙ DerivedCategory.Q)
    (T.obj (DerivedCategory.Q.obj K)) K.kFlatTensor (Iso.refl _)

/-- Compatibility of `derivedTensorObjIsoKFlatTensor` with the derived tensor comparison `α` and
`kFlatTensorModelIso`. -/
@[reassoc (attr := simp)]
lemma derivedTensorObjIsoKFlatTensor_hom_app_Q
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    (derivedTensorObjIsoKFlatTensor T α K).hom.app (DerivedCategory.Q.obj L) ≫
      K.kFlatTensorModelIso.hom.app L = (α.app K).app L := by
  rw [kFlatTensorModelIso_eq_liftingIso]
  simp only [derivedTensorObjIsoKFlatTensor, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.iso, Iso.trans_hom, asIso_hom,
    Functor.bifunctorCounit₁_app, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Category.comp_id, Category.assoc, Iso.inv_hom_id_app]
  dsimp [NatIso.ofComponents]
  simp

/-- **Left unit isomorphism for the derived tensor product.** Derived tensoring on the left with
`R[0]` is naturally isomorphic to the identity functor of `DerivedCategory (ModuleCat.{u} R)`. -/
def derivedTensorLeftUnitIso :
    T.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} R)) := by
  haveI : IsIso (Functor.bifunctorCounit₁ α (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro L
    exact isIso_derivedTensorCounit_of_isKFlat_left T α _ L
  haveI : Localization.Lifting DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
      (tensorLeft (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⋙ DerivedCategory.Q)
      (T.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))) :=
    ⟨asIso (Functor.bifunctorCounit₁ α (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))⟩
  haveI : Localization.Lifting DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
      DerivedCategory.Q (𝟭 (DerivedCategory (ModuleCat.{u} R))) :=
    ⟨Functor.rightUnitor _⟩
  exact Localization.liftNatIso DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
    (tensorLeft (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⋙ DerivedCategory.Q)
    DerivedCategory.Q _ _
    (Functor.isoWhiskerRight (leftUnitorNatIso (CochainComplex (ModuleCat.{u} R) ℤ))
      DerivedCategory.Q)

/-- Value of `derivedTensorLeftUnitIso` on the image of a cochain complex. -/
@[simp, reassoc]
lemma derivedTensorLeftUnitIso_hom_app_Q (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedTensorLeftUnitIso T α).hom.app (DerivedCategory.Q.obj L) =
      (α.app (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).app L ≫
        DerivedCategory.Q.map (λ_ L).hom := by
  simp [derivedTensorLeftUnitIso, Localization.Lifting.iso]

/-- **Right unit isomorphism for the derived tensor product.** Derived tensoring on the right with
`R[0]` is naturally isomorphic to the identity functor of `DerivedCategory (ModuleCat.{u} R)`. -/
def derivedTensorRightUnitIso :
    T.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} R)) := by
  haveI : IsIso (Functor.bifunctorCounit₂ α (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact isIso_derivedTensorCounit_of_isKFlat_right T α K _
  haveI : Localization.Lifting DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
      (tensorRight (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⋙ DerivedCategory.Q)
      (T.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))) :=
    ⟨asIso (Functor.bifunctorCounit₂ α (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))⟩
  haveI : Localization.Lifting DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
      DerivedCategory.Q (𝟭 (DerivedCategory (ModuleCat.{u} R))) :=
    ⟨Functor.rightUnitor _⟩
  exact Localization.liftNatIso DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
    (tensorRight (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⋙ DerivedCategory.Q)
    DerivedCategory.Q _ _
    (Functor.isoWhiskerRight (rightUnitorNatIso (CochainComplex (ModuleCat.{u} R) ℤ))
      DerivedCategory.Q)

/-- Value of `derivedTensorRightUnitIso` on the image of a cochain complex. -/
@[simp, reassoc]
lemma derivedTensorRightUnitIso_hom_app_Q (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedTensorRightUnitIso T α).hom.app (DerivedCategory.Q.obj K) =
      (α.app K).app (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ≫
        DerivedCategory.Q.map (ρ_ K).hom := by
  simp [derivedTensorRightUnitIso, Localization.Lifting.iso]

/-- The Koszul braiding as a natural transformation from the flipped tensor bifunctor to the
tensor bifunctor, post-composed with localization. -/
private def koszulBraidingCounit :
    (((Functor.whiskeringLeft₂ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R))).obj
      DerivedCategory.Q).obj T.flip ⟶
      curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q where
  app K :=
    { app L := (α.app L).app K ≫ DerivedCategory.Q.map (β_ L K).hom
      naturality L₁ L₂ g := by
        have h := congr_app (α.naturality g) K
        dsimp at h ⊢
        rw [reassoc_of% h, Category.assoc, ← DerivedCategory.Q.map_comp,
          ← DerivedCategory.Q.map_comp, BraidedCategory.braiding_naturality_left] }
  naturality K₁ K₂ f := by
    ext L
    have h := (α.app L).naturality f
    dsimp at h ⊢
    rw [reassoc_of% h, Category.assoc, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp, BraidedCategory.braiding_naturality_right]

/-- **Symmetry of the derived tensor product.** The Koszul braiding induces an involutive natural
isomorphism `T.flip ≅ T` on any left derived tensor bifunctor `T`. -/
def derivedTensorFlipIso : T.flip ≅ T :=
  let φ : T.flip ⟶ T :=
    T.leftDerived₂Lift α (quasiIso (ModuleCat.{u} R) (.up ℤ))
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) T.flip (koszulBraidingCounit T α)
  let ψ : T ⟶ T.flip := (flipFunctor _ _ _).map φ
  have hψφ : ψ ≫ φ = 𝟙 T :=
    T.leftDerived₂_ext α (quasiIso (ModuleCat.{u} R) (.up ℤ))
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (hγ := by
        ext K L
        have h₁ := T.leftDerived₂_fac_app_app α (quasiIso (ModuleCat.{u} R) (.up ℤ))
          (quasiIso (ModuleCat.{u} R) (.up ℤ)) T.flip (koszulBraidingCounit T α) K L
        have h₂ := T.leftDerived₂_fac_app_app α (quasiIso (ModuleCat.{u} R) (.up ℤ))
          (quasiIso (ModuleCat.{u} R) (.up ℤ)) T.flip (koszulBraidingCounit T α) L K
        dsimp [φ, ψ, koszulBraidingCounit] at h₁ h₂ ⊢
        rw [Category.assoc, h₁, reassoc_of% h₂, ← DerivedCategory.Q.map_comp,
          SymmetricCategory.symmetry, DerivedCategory.Q.map_id, Category.comp_id, Category.id_comp])
  { hom := φ
    inv := ψ
    hom_inv_id := by
      ext X Y
      exact congr_app (congr_app hψφ Y) X
    inv_hom_id := hψφ }

/-- The inverse of `derivedTensorFlipIso` at `(X, Y)` is its forward map at `(Y, X)`. -/
@[simp]
lemma derivedTensorFlipIso_inv_app_app (X Y : DerivedCategory (ModuleCat.{u} R)) :
    ((derivedTensorFlipIso T α).inv.app X).app Y =
      ((derivedTensorFlipIso T α).hom.app Y).app X := (rfl)

/-- Involutivity of `derivedTensorFlipIso`: applying the symmetry twice is the identity. -/
@[reassoc (attr := simp)]
lemma derivedTensorFlipIso_hom_app_app_comp (X Y : DerivedCategory (ModuleCat.{u} R)) :
    ((derivedTensorFlipIso T α).hom.app X).app Y ≫
      ((derivedTensorFlipIso T α).hom.app Y).app X = 𝟙 ((T.obj Y).obj X) :=
  congr_app (congr_app (derivedTensorFlipIso T α).hom_inv_id X) Y

/-- Compatibility of `derivedTensorFlipIso` with the Koszul braiding on images of complexes. -/
@[reassoc (attr := simp)]
lemma derivedTensorFlipIso_hom_app_app_Q
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((derivedTensorFlipIso T α).hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
      (α.app K).app L =
    (α.app L).app K ≫ DerivedCategory.Q.map (β_ L K).hom :=
  T.leftDerived₂_fac_app_app α (quasiIso (ModuleCat.{u} R) (.up ℤ))
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) T.flip (koszulBraidingCounit T α) K L

end ModelComparison

end DerivedTensor

end CochainComplex
