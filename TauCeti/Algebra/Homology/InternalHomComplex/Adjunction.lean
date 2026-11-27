/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Localization.Adjunction
public import TauCeti.Algebra.Homology.HomotopyCategory.Bifunctor
public import TauCeti.Algebra.Homology.InternalHomComplex.Curry
public import TauCeti.Algebra.Homology.InternalHomComplex.Homotopy
public import TauCeti.Algebra.Homology.Monoidal.KFlat.Basic

/-!
# The tensor-Hom adjunction for the internal Hom complex

Let `C` be a closed monoidal preadditive category with countable products in which all tensor
products of cochain complexes exist, and let `P` be a cochain complex in `C`. Currying
(`TauCeti.tensorObjInternalHomComplexHomEquiv`) makes tensoring on the left with `P` left adjoint
to the internal Hom complex `𝓗om^•(P, -)` out of `P`
(`TauCeti.tensorLeftInternalHomComplexAdjunction`). Currying also matches homotopies with
homotopies (`TauCeti.tensorObjInternalHomComplexHomEquivHomotopy`), so the adjunction descends to
homotopy categories (`TauCeti.tensorLeftInternalHomComplexHomotopyAdjunction`), where `P ⊗ -` is
the totalized tensor bifunctor `CategoryTheory.Functor.map₂HomotopyCategory` and `𝓗om^•(P, -)` is
`TauCeti.internalHomComplexHomotopyFunctor`.

If `C` is abelian, `P` is K-flat and `I` is K-injective, then `𝓗om^•(P, I)` is K-injective
(`TauCeti.isKInjective_internalHomComplex`): a map from an acyclic complex `A` to `𝓗om^•(P, I)`
uncurries to a map from the acyclic complex `P ⊗ A` to `I`. This is the input from which the
derived tensor-Hom adjunction `L ⊗^L - ⊣ R𝓗om(L, -)` on the unbounded derived category is built.

## Main definitions

* `TauCeti.tensorObjInternalHomComplexHomEquivHomotopy`: homotopies between morphisms
  `P ⊗ L ⟶ M` correspond to homotopies between their curried forms `L ⟶ 𝓗om^•(P, M)`.
* `TauCeti.tensorLeftInternalHomComplexAdjunction`: the adjunction `P ⊗ - ⊣ 𝓗om^•(P, -)` on
  cochain complexes.
* `TauCeti.tensorLeftInternalHomComplexHomotopyAdjunction`: the same adjunction on homotopy
  categories.

## Main results

* `TauCeti.tensorLeftInternalHomComplexHomotopyAdjunction_homEquiv_quotient_map`: on homotopy
  classes of chain maps, the adjunction on homotopy categories is currying.
* `TauCeti.isKInjective_internalHomComplex`: the internal Hom complex from a K-flat complex to a
  K-injective complex is K-injective.

## Implementation notes

This file is the closed monoidal analogue of the adjunction part of
`TauCeti/Algebra/Homology/LinearHomComplex/Curry.lean`. Since Mathlib's internal Hom is right
adjoint to tensoring on the left, the curried variable is the second tensor factor, and K-flatness
(tensoring on the left preserves acyclicity) is used without any braiding.

## References

* [Stacks Project, Lemma 15.73.1 (0A5Y)](https://stacks.math.columbia.edu/tag/0A5Y) and
  [Stacks Project, Lemma 20.42.1 (08DI)](https://stacks.math.columbia.edu/tag/08DI).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [HasCountableProducts C]

section Homotopy

variable {K L M : CochainComplex C ℤ} [HasTensor K L]

/-- Homotopies between morphisms `K ⊗ L ⟶ M` correspond to homotopies between their curried
forms `L ⟶ 𝓗om^•(K, M)`. -/
def tensorObjInternalHomComplexHomEquivHomotopy (f g : tensorObj K L ⟶ M) :
    Homotopy f g ≃ Homotopy (tensorObjInternalHomComplexHomEquiv K L M f)
      (tensorObjInternalHomComplexHomEquiv K L M g) :=
  (Cochain.equivHomotopy f g).trans <|
    (Equiv.subtypeEquiv (Cochain.curryInternalHomAddEquiv K L M (-1)).toEquiv fun z => by
      simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
        ofHom_tensorObjInternalHomComplexHomEquiv, Cochain.curryInternalHomAddEquiv_apply]
      rw [Cochain.δ_curryInternalHom, ← Cochain.curryInternalHomAddEquiv_apply,
        ← Cochain.curryInternalHomAddEquiv_apply, ← Cochain.curryInternalHomAddEquiv_apply,
        ← map_add, (Cochain.curryInternalHomAddEquiv K L M 0).injective.eq_iff]).trans
      (Cochain.equivHomotopy _ _).symm

/-- `(tensorObjInternalHomComplexHomEquiv K L M).symm` is natural in the second tensor factor. -/
lemma tensorObjInternalHomComplexHomEquiv_symm_naturality_snd {L' : CochainComplex C ℤ}
    [HasTensor K L'] (g : L' ⟶ L) (f : L ⟶ internalHomComplex K M) :
    (tensorObjInternalHomComplexHomEquiv K L' M).symm (g ≫ f) =
      tensorHom (𝟙 K) g ≫ (tensorObjInternalHomComplexHomEquiv K L M).symm f := by
  rw [Equiv.symm_apply_eq, tensorObjInternalHomComplexHomEquiv_naturality_snd,
    Equiv.apply_symm_apply]

end Homotopy

section Adjunction

variable [∀ K L : CochainComplex C ℤ, HasTensor K L] (P : CochainComplex C ℤ)

/-- **Tensor–Hom adjunction for cochain complexes.** Tensoring on the left with `P` is left
adjoint to the internal Hom complex `𝓗om^•(P, -)` out of `P`: morphisms `P ⊗ L ⟶ M` correspond to
morphisms `L ⟶ 𝓗om^•(P, M)` by currying (`tensorObjInternalHomComplexHomEquiv`). -/
def tensorLeftInternalHomComplexAdjunction :
    ((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj P ⊣
      (internalHomComplexFunctor C).obj (Opposite.op P) :=
  Adjunction.mkOfHomEquiv
    { homEquiv L M := tensorObjInternalHomComplexHomEquiv P L M
      homEquiv_naturality_left_symm f g :=
        tensorObjInternalHomComplexHomEquiv_symm_naturality_snd f g
      homEquiv_naturality_right f g := tensorObjInternalHomComplexHomEquiv_naturality_target f g }

@[simp]
lemma tensorLeftInternalHomComplexAdjunction_homEquiv (L M : CochainComplex C ℤ) :
    (tensorLeftInternalHomComplexAdjunction P).homEquiv L M =
      tensorObjInternalHomComplexHomEquiv P L M := by
  rw [tensorLeftInternalHomComplexAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- On homotopy categories, tensoring on the left with the class of `P` is induced by tensoring
complexes on the left with `P`. The square commutes on the nose, by
`Functor.map₂HomotopyCategory`. -/
private instance catCommSqTensorLeftQuotient :
    CatCommSq (((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj P)
      (HomotopyCategory.quotient C (.up ℤ)) (HomotopyCategory.quotient _ _)
      (((curriedTensor C).map₂HomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) :=
  ⟨Iso.refl _⟩

/-- On homotopy categories, the internal Hom complex out of the class of `P` is induced by the
internal Hom complex out of `P`. The square commutes on the nose, by
`internalHomComplexHomotopyFunctor`. -/
private instance catCommSqInternalHomComplexFunctorQuotient :
    CatCommSq ((internalHomComplexFunctor C).obj (Opposite.op P))
      (HomotopyCategory.quotient C (.up ℤ)) (HomotopyCategory.quotient _ _)
      ((internalHomComplexHomotopyFunctor C).obj
        (Opposite.op ((HomotopyCategory.quotient _ _).obj P))) :=
  ⟨Iso.refl _⟩

/-- **Tensor–Hom adjunction on homotopy categories.** Tensoring on the left with the class of `P`
is left adjoint to the internal Hom complex out of `P` on the homotopy category of complexes: it
is the localization (`Adjunction.localization`) of `tensorLeftInternalHomComplexAdjunction` along
`HomotopyCategory.quotient`, the localization at homotopy equivalences. -/
def tensorLeftInternalHomComplexHomotopyAdjunction :
    ((curriedTensor C).map₂HomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P) ⊣
      (internalHomComplexHomotopyFunctor C).obj
        (Opposite.op ((HomotopyCategory.quotient _ _).obj P)) :=
  -- `HomotopyCategory.quotient` is the localization at homotopy equivalences once `C` has binary
  -- biproducts, which follow from its countable products since `C` is preadditive.
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  (tensorLeftInternalHomComplexAdjunction P).localization (HomotopyCategory.quotient _ _)
    (homotopyEquivalences _ _) (HomotopyCategory.quotient _ _) (homotopyEquivalences _ _) _ _

variable {P} in
/-- On homotopy classes of chain maps, the adjunction on homotopy categories is currying. -/
lemma tensorLeftInternalHomComplexHomotopyAdjunction_homEquiv_quotient_map
    {L M : CochainComplex C ℤ} (f : tensorObj P L ⟶ M) :
    (tensorLeftInternalHomComplexHomotopyAdjunction P).homEquiv
        ((HomotopyCategory.quotient _ _).obj L) ((HomotopyCategory.quotient _ _).obj M)
        ((HomotopyCategory.quotient _ _).map f) =
      (HomotopyCategory.quotient _ _).map (tensorObjInternalHomComplexHomEquiv P L M f) := by
  have h : tensorObjInternalHomComplexHomEquiv P L M f =
      (tensorLeftInternalHomComplexAdjunction P).unit.app L ≫
        ((internalHomComplexFunctor C).obj (Opposite.op P)).map f := by
    rw [← tensorLeftInternalHomComplexAdjunction_homEquiv]
    exact Adjunction.homEquiv_unit _ _ _ _
  refine ((tensorLeftInternalHomComplexHomotopyAdjunction P).homEquiv_unit _ _ _).trans
    (Eq.trans ?_ (congrArg _ h.symm))
  simp only [tensorLeftInternalHomComplexHomotopyAdjunction, Adjunction.localization_unit_app,
    CatCommSq.iso, Iso.refl_hom, NatTrans.id_app]
  -- Both comparison squares are identities. Their objects agree with those of the adjacent
  -- morphisms only up to `Functor.comp_obj` and `internalHomComplexHomotopyFunctor_obj_obj`, so
  -- the identities are removed with `erw`.
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  -- The image of `quotient.map f` is `quotient.map` of the postcomposition with `f`, by
  -- `internalHomComplexHomotopyFunctor_obj_map`.
  exact (Functor.map_comp _ _ _).symm

end Adjunction

section KInjective

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [HasCountableProducts C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- The internal Hom complex from a K-flat complex to a K-injective complex is K-injective. -/
instance isKInjective_internalHomComplex (P I : CochainComplex C ℤ) [P.IsKFlat]
    [I.IsKInjective] : (internalHomComplex P I).IsKInjective where
  nonempty_homotopy_zero {A} f hA := by
    obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero
      ((tensorObjInternalHomComplexHomEquiv P A I).symm f) (IsKFlat.acyclic_tensor A hA)
    exact ⟨(Homotopy.ofEq (by simp)).trans
      ((tensorObjInternalHomComplexHomEquivHomotopy _ _ h).trans (Homotopy.ofEq (by
        refine Cochain.ofHom_injective ?_
        simp)))⟩

end KInjective

end TauCeti
