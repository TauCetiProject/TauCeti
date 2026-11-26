/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import TauCeti.Algebra.Homology.DerivedCategory.InternalHom.Basic
public import TauCeti.Algebra.Homology.InternalHomComplex.Adjunction
public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor

/-!
# The derived tensor–internal Hom adjunction

Let `C` be a closed braided monoidal abelian category with countable products, in which every
unbounded complex has a K-injective replacement and K-flat complexes form a left derivability
structure; for instance the category of `𝒪_X`-modules on a scheme `X`. Assume moreover that `C`
has a separating family of objects `G` for which `- ⊗ G` preserves acyclic complexes. Then for
every left derived bifunctor `T` of the totalized tensor product of complexes (for instance
`TauCeti.derivedTensor C`) and every `L` in `D(C)`, the functor `K ↦ T(L, K) = L ⊗^L K` is left
adjoint to the derived internal Hom `M ↦ R𝓗om(L, M)` of `TauCeti.derivedInternalHom`:

`Hom_{D(C)}(L ⊗^L K, M) ≃ Hom_{D(C)}(K, R𝓗om(L, M))`

naturally in `K` and `M` (`TauCeti.derivedTensorInternalHomAdj`). No boundedness is assumed.
Applied to `L = 𝟙_ C` in degree `0`, the derived left unitor gives `R𝓗om(𝟙_ C, M) ≅ M`
(`TauCeti.derivedInternalHomSingleUnitIso`).

The construction follows the Stacks Project and `TauCeti.derivedTensorHomAdj` for modules.
Represent `L` by a K-flat complex `P`. Currying is an adjunction `P ⊗ - ⊣ 𝓗om^•(P, -)` on the
homotopy category of complexes (`TauCeti.tensorLeftInternalHomComplexHomotopyAdjunction`).
Composing it with the adjunction `DerivedCategory.Qh ⊣ TauCeti.kInjectiveReplacement` gives an
adjunction between the homotopy category and `D(C)`. Since `P` is K-flat, `P ⊗ -` computes
`T(P, -)` (`TauCeti.qhCompObjIsoOfIsKFlat`), and since `𝓗om^•(P, I)` is K-injective for
K-injective `I` (`TauCeti.isKInjective_internalHomComplex`), the right adjoint takes values in
the image of the fully faithful functor `TauCeti.kInjectiveReplacement`. Restricting along that
functor gives the model adjunction `TauCeti.derivedTensorInternalHomAdjOfIsKFlat`. Finally, when
`P` maps quasi-isomorphically to the K-injective replacement of `L`, precomposition identifies
`𝓗om^•(P, I)` with `R𝓗om(L, -)` (`TauCeti.derivedInternalHomObjIsoOfQuasiIso`); this is where the
separating family is used (`TauCeti.quasiIso_internalHomComplexPrecomp`).

## Main definitions

* `TauCeti.derivedTensorInternalHomAdjOfIsKFlat`: for a K-flat complex `P`, the adjunction between
  `T(P, -)` and the internal Hom complex out of `P` into K-injective replacements.
* `TauCeti.derivedTensorInternalHomAdjOfQuasiIso`: the derived tensor–internal Hom adjunction
  `T(L, -) ⊣ R𝓗om(L, -)` built from a given K-flat complex with a quasi-isomorphism to the
  K-injective replacement of `L`.
* `TauCeti.derivedTensorInternalHomAdj`: the derived tensor–internal Hom adjunction
  `T(L, -) ⊣ R𝓗om(L, -)`, built from a chosen such model.
* `TauCeti.derivedInternalHomSingleUnitIso`: `R𝓗om(𝟙_ C[0], -)` is the identity functor.

## Main results

* `TauCeti.exists_derivedTensorInternalHomAdj_eq`: `TauCeti.derivedTensorInternalHomAdj` is
  `TauCeti.derivedTensorInternalHomAdjOfQuasiIso` for some K-flat model.
* `TauCeti.derivedTensorInternalHomAdjOfIsKFlat_homEquiv` and
  `TauCeti.derivedTensorInternalHomAdjOfQuasiIso_homEquiv`: the bijections of these adjunctions, in
  terms of currying on homotopy categories.

## References

* [Stacks Project, Lemma 20.42.1 (08DI)](https://stacks.math.columbia.edu/tag/08DI) and
  [Stacks Project, Section 21.35 (08J7)](https://stacks.math.columbia.edu/tag/08J7).
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory DerivedCategory CochainComplex Opposite

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [HasCountableProducts C] [HasKInjectiveResolutions C]
  [HasDerivedCategory.{w} C]

variable [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory C] [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]

section KFlatModel

variable (T : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C)
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj T ⟶
    curriedTensor (CochainComplex C ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
  [T.IsLeftDerivedFunctor₂ α (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))]

include α

/-- **Tensor–internal Hom adjunction on K-flat models.** For a K-flat complex `P`, the derived
tensor product `T(P, -)` is left adjoint to the functor sending `M` to the internal Hom complex out
of `P` into the K-injective replacement of `M`. -/
def derivedTensorInternalHomAdjOfIsKFlat (P : CochainComplex C ℤ) [P.IsKFlat] :
    T.obj (Q.obj P) ⊣ kInjectiveReplacement C ⋙
      (internalHomComplexHomotopyFunctor C).obj (op ((HomotopyCategory.quotient _ _).obj P)) ⋙
        Qh :=
  ((tensorLeftInternalHomComplexHomotopyAdjunction P).comp
    (kInjectiveReplacementAdjunction _)).restrictFullyFaithful
    (fullyFaithfulKInjectiveReplacement _) (Functor.FullyFaithful.id _)
    (Functor.isoWhiskerLeft _ (qhCompObjIsoOfIsKFlat T α P).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (kInjectiveReplacementAdjunction _).counit) _ ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    -- The internal Hom complex out of the K-flat `P` into a K-injective complex is K-injective,
    -- so the unit of `Qh ⊣ kInjectiveReplacement` is an isomorphism on it.
    (NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ _
      ((kInjectiveReplacementAdjunction _).isIso_unit_app_iff_mem_essImage.2
        ((mem_essImage_kInjectiveReplacement_iff _).2
          (isKInjective_internalHomComplex P ((kInjectiveReplacement _).obj M).as))))
      (fun _ ↦ (kInjectiveReplacementAdjunction _).unit.naturality _))

/-- Under the fully faithful functor `kInjectiveReplacement`, the bijection of
`derivedTensorInternalHomAdjOfIsKFlat` is currying on homotopy categories
(`tensorLeftInternalHomComplexHomotopyAdjunction`) composed with the adjunction
`Qh ⊣ kInjectiveReplacement`, after identifying `T(P, X)` with the tensor product of `P` with the
K-injective replacement of `X` (`qhCompObjIsoOfIsKFlat`). -/
lemma derivedTensorInternalHomAdjOfIsKFlat_homEquiv (P : CochainComplex C ℤ) [P.IsKFlat]
    (X Y : DerivedCategory C) (f : (T.obj (Q.obj P)).obj X ⟶ Y) :
    (kInjectiveReplacement _).map ((derivedTensorInternalHomAdjOfIsKFlat T α P).homEquiv X Y f) =
      (tensorLeftInternalHomComplexHomotopyAdjunction P).homEquiv _ _
          ((kInjectiveReplacementAdjunction _).homEquiv _ _
            ((qhCompObjIsoOfIsKFlat T α P).inv.app ((kInjectiveReplacement _).obj X) ≫
              (T.obj (Q.obj P)).map ((kInjectiveReplacementAdjunction _).counit.app X) ≫ f)) ≫
        (kInjectiveReplacementAdjunction _).unit.app
          (((internalHomComplexHomotopyFunctor C).obj
            (op ((HomotopyCategory.quotient _ _).obj P))).obj
              ((kInjectiveReplacement _).obj Y)) := by
  rw [derivedTensorInternalHomAdjOfIsKFlat, Adjunction.restrictFullyFaithful_homEquiv_apply,
    Functor.FullyFaithful.map_preimage]
  simp [Adjunction.homEquiv_unit]

end KFlatModel

section Separating

variable {S : ObjectProperty C} (hS : S.IsSeparating)
  (hSacyclic : ∀ G, S G → ∀ X : CochainComplex C ℤ, X.Acyclic →
    (((tensorRight G).mapHomologicalComplex _).obj X).Acyclic)

include hS hSacyclic

variable (T : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C)
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj T ⟶
    curriedTensor (CochainComplex C ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
  [T.IsLeftDerivedFunctor₂ α (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))]

include α

/-- **The derived tensor–internal Hom adjunction on a K-flat model.** Let `C` have a separating
family of objects `G` for which `- ⊗ G` preserves acyclic complexes. For every left derived
bifunctor `T` of the tensor product of complexes, every `L` in `D(C)` and every K-flat complex `P`
with a quasi-isomorphism `p` to the K-injective replacement of `L`, the functor `K ↦ T(L, K)` is
left adjoint to the derived internal Hom `M ↦ R𝓗om(L, M)`. It is
`derivedTensorInternalHomAdjOfIsKFlat` transported along the identification of `Q.obj P` with `L`
and along `derivedInternalHomObjIsoOfQuasiIso`. -/
def derivedTensorInternalHomAdjOfQuasiIso (L : DerivedCategory C) {P : CochainComplex C ℤ}
    [P.IsKFlat] (p : P ⟶ ((kInjectiveReplacement C).obj L).as) [QuasiIso p] :
    T.obj L ⊣ (derivedInternalHom C).obj (op L) :=
  ((derivedTensorInternalHomAdjOfIsKFlat T α P).ofNatIsoLeft
    (T.mapIso (((asIso (kInjectiveReplacementAdjunction C).counit).app L).symm ≪≫
      (quotientCompQhIso C).app _ ≪≫ (asIso (Q.map p)).symm)).symm).ofNatIsoRight
    (derivedInternalHomObjIsoOfQuasiIso hS hSacyclic L p).symm

/-- The bijection of `derivedTensorInternalHomAdjOfQuasiIso` is that of
`derivedTensorInternalHomAdjOfIsKFlat`, conjugated by the identification of `Q.obj P` with `L` and
by `derivedInternalHomObjIsoOfQuasiIso`. -/
lemma derivedTensorInternalHomAdjOfQuasiIso_homEquiv (L : DerivedCategory C)
    {P : CochainComplex C ℤ} [P.IsKFlat] (p : P ⟶ ((kInjectiveReplacement C).obj L).as)
    [QuasiIso p] (X Y : DerivedCategory C) (f : (T.obj L).obj X ⟶ Y) :
    (derivedTensorInternalHomAdjOfQuasiIso hS hSacyclic T α L p).homEquiv X Y f =
      (derivedTensorInternalHomAdjOfIsKFlat T α P).homEquiv X Y
          ((T.map (Q.map p ≫ (quotientCompQhIso C).inv.app _ ≫
            (kInjectiveReplacementAdjunction C).counit.app L)).app X ≫ f) ≫
        (derivedInternalHomObjIsoOfQuasiIso hS hSacyclic L p).inv.app Y := by
  simp [derivedTensorInternalHomAdjOfQuasiIso, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.homEquiv_ofNatIsoRight_apply]

/-- **The derived tensor–internal Hom adjunction.** Let `C` have a separating family of objects
`G` for which `- ⊗ G` preserves acyclic complexes. For every left derived bifunctor `T` of the
tensor product of complexes and every `L` in `D(C)`, the functor `K ↦ T(L, K) = L ⊗^L K` is left
adjoint to the derived internal Hom `M ↦ R𝓗om(L, M)`, so that
`Hom(L ⊗^L K, M) ≃ Hom(K, R𝓗om(L, M))` naturally in `K` and `M`. It is
`derivedTensorInternalHomAdjOfQuasiIso` for a chosen K-flat complex with a quasi-isomorphism to
the K-injective replacement of `L`. -/
def derivedTensorInternalHomAdj (L : DerivedCategory C) :
    T.obj L ⊣ (derivedInternalHom C).obj (op L) :=
  let h := exists_quasiIso_isKFlat_of_hasLeftResolutions ((kInjectiveReplacement C).obj L).as
  have : h.choose.IsKFlat := h.choose_spec.choose_spec.2
  have : QuasiIso h.choose_spec.choose := h.choose_spec.choose_spec.1
  derivedTensorInternalHomAdjOfQuasiIso hS hSacyclic T α L h.choose_spec.choose

/-- The adjunction `derivedTensorInternalHomAdj` is `derivedTensorInternalHomAdjOfQuasiIso` for
some K-flat complex `P` with a quasi-isomorphism `p` to the K-injective replacement of `L`, so its
bijection is described by `derivedTensorInternalHomAdjOfQuasiIso_homEquiv`. -/
lemma exists_derivedTensorInternalHomAdj_eq (L : DerivedCategory C) :
    ∃ (P : CochainComplex C ℤ) (_ : P.IsKFlat)
      (p : P ⟶ ((kInjectiveReplacement C).obj L).as) (_ : QuasiIso p),
      derivedTensorInternalHomAdj hS hSacyclic T α L =
        derivedTensorInternalHomAdjOfQuasiIso hS hSacyclic T α L p :=
  ⟨_, _, _, _, rfl⟩

end Separating

variable (C) in
/-- Let `C` have a separating family of objects `G` for which `- ⊗ G` preserves acyclic
complexes. The derived internal Hom `R𝓗om(𝟙_ C[0], -)` out of the unit placed in degree `0` is
the identity functor: both are right adjoint to `𝟙_ C[0] ⊗^L - ≅ 𝟭`
(`derivedTensorInternalHomAdj`, `derivedTensorLeftUnitor`). -/
def derivedInternalHomSingleUnitIso {S : ObjectProperty C} (hS : S.IsSeparating)
    (hSacyclic : ∀ G, S G → ∀ X : CochainComplex C ℤ, X.Acyclic →
      (((tensorRight G).mapHomologicalComplex _).obj X).Acyclic) :
    (derivedInternalHom C).obj (op ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))) ≅ 𝟭 _ :=
  ((derivedTensorInternalHomAdj hS hSacyclic (derivedTensor C) (derivedTensorCounit C)
    _).ofNatIsoLeft (derivedTensorLeftUnitor C)).rightAdjointUniq Adjunction.id

end TauCeti
