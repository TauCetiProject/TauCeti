/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# The K-flat left derivability structure

Let `C` be an abelian monoidal category in which tensoring is additive in each variable and total
tensor products of cochain complexes exist. The full subcategory inclusion of K-flat complexes into
`CochainComplex C ℤ`, equipped with the induced class of quasi-isomorphisms, defines a localizer
morphism `CochainComplex.kFlatLocalizerMorphism C`.

Whenever countable coproducts and sequential colimits in `C` are exact and commute with tensoring
on the right, and `C` admits a functorial cover `p : E ⟶ 𝟭 C` by flat objects (`E.obj X` flat and
`p.app X` epimorphic for every `X`), the functorial cell-attaching resolution
`CochainComplex.kFlatResolutionFunctor E p` lifts to the full subcategory of K-flat complexes and
makes `CochainComplex.kFlatLocalizerMorphism C` a left derivability structure
(`CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism`), inducing an equivalence on
derived localizations and supplying left resolutions of arrows.

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
* The Stacks Project, More on Algebra, Section 15.60, K-flat complexes.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

variable (C : Type*) [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- The object property of K-flat cochain complexes in `C`. -/
abbrev isKFlat : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ K.IsKFlat

instance (P : (isKFlat C).FullSubcategory) : P.obj.IsKFlat := P.property

/-- The localizer morphism given by the inclusion of the full subcategory of K-flat complexes into
`CochainComplex C ℤ`, with respect to quasi-isomorphisms. -/
abbrev kFlatLocalizerMorphism :
    LocalizerMorphism ((quasiIso C (.up ℤ)).inverseImage (isKFlat C).ι)
      (quasiIso C (.up ℤ)) where
  functor := (isKFlat C).ι
  map := by rfl

instance : (kFlatLocalizerMorphism C).IsInduced where
  inverseImage_eq := rfl

section FunctorialCover

variable {C}
variable [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
  (E : C ⥤ C) (p : E ⟶ 𝟭 C)
  [∀ X, Epi (p.app X)]
  [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
  [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))]

/-- The lift of `kFlatResolutionFunctor E p` to the full subcategory of K-flat complexes. -/
private def kFlatResolutionLiftFunctor :
    CochainComplex C ℤ ⥤ (isKFlat C).FullSubcategory :=
  (isKFlat C).lift (kFlatResolutionFunctor E p) fun K ↦
    inferInstanceAs ((kFlatResolutionFunctor E p).obj K).IsKFlat

/-- The augmentation from the lifted K-flat resolution functor composed with the subcategory
inclusion to the identity functor on `CochainComplex C ℤ`. -/
private def kFlatResolutionLiftAugmentation :
    kFlatResolutionLiftFunctor E p ⋙ (kFlatLocalizerMorphism C).functor ⟶
      𝟭 (CochainComplex C ℤ) :=
  ((isKFlat C).liftCompιIso (kFlatResolutionFunctor E p) _).hom ≫
    kFlatResolution.πNatTrans E p

private lemma mem_quasiIso_kFlatResolutionLiftAugmentation_app (K : CochainComplex C ℤ) :
    quasiIso C (.up ℤ) ((kFlatResolutionLiftAugmentation E p).app K) := by
  let e := ((isKFlat C).liftCompιIso (kFlatResolutionFunctor E p) fun K ↦
    inferInstanceAs ((kFlatResolutionFunctor E p).obj K).IsKFlat).app K
  exact (quasiIso C (.up ℤ)).comp_mem e.hom _ (MorphismProperty.of_isIso _ _)
    ((mem_quasiIso_iff _).2 inferInstance)

include E p

/-- In an abelian monoidal category with functorial flat covers and exact countable coproducts and
sequential colimits commuting with tensor products, `kFlatLocalizerMorphism C` has left resolutions
of arrows. -/
theorem hasLeftResolutions_arrow_kFlatLocalizerMorphism :
    (kFlatLocalizerMorphism C).arrow.HasLeftResolutions :=
  (kFlatLocalizerMorphism C).hasLeftResolutions_arrow_of_functorial_resolutions
    (kFlatResolutionLiftAugmentation E p)
    (mem_quasiIso_kFlatResolutionLiftAugmentation_app E p)

/-- In an abelian monoidal category with functorial flat covers and exact countable coproducts and
sequential colimits commuting with tensor products, the inclusion of K-flat complexes induces an
equivalence on localized categories. -/
theorem isLocalizedEquivalence_kFlatLocalizerMorphism :
    (kFlatLocalizerMorphism C).IsLocalizedEquivalence :=
  (kFlatLocalizerMorphism C).isLocalizedEquivalence_of_functorial_left_resolutions
    (kFlatResolutionLiftAugmentation E p)
    (mem_quasiIso_kFlatResolutionLiftAugmentation_app E p) rfl

/-- **The K-flat left derivability structure.** In an abelian monoidal category with functorial
flat covers and exact countable coproducts and sequential colimits commuting with tensor products,
the inclusion `kFlatLocalizerMorphism C` of K-flat complexes into `CochainComplex C ℤ` is a left
derivability structure with respect to quasi-isomorphisms. -/
theorem isLeftDerivabilityStructure_kFlatLocalizerMorphism :
    (kFlatLocalizerMorphism C).IsLeftDerivabilityStructure :=
  (kFlatLocalizerMorphism C).isLeftDerivabilityStructure_of_functorial_resolutions
    (kFlatResolutionLiftAugmentation E p)
    (mem_quasiIso_kFlatResolutionLiftAugmentation_app E p) rfl

end FunctorialCover

end CochainComplex
