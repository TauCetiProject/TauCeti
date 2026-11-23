/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Single

/-!
# Bifunctor totalizations with a single complex

The partial differential of `mapBifunctor A[j] K F c` or `mapBifunctor K A[j] F c` that would
differentiate the single complex `A[j]` vanishes, for any zero-preserving bifunctor `F` and any
total complex shape `c`.

## Main results

* `HomologicalComplex.single_mapBifunctor_d₁`: the first partial differential of
  `mapBifunctor A[j] K F c` vanishes.
* `HomologicalComplex.mapBifunctor_single_d₂`: the second partial differential of
  `mapBifunctor K A[j] F c` vanishes.
-/

public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]

/-- The first partial differential of `mapBifunctor A[j] K F c` vanishes, as the differential of
the single complex `A[j]` does. Mathlib's `HomologicalComplex.unit_tensor_d₁` is the case of the
tensor product with the monoidal unit in degree `0`; the proof is that of Mathlib's
`HomologicalComplex.unit_tensor_d₁`. -/
@[simp]
lemma single_mapBifunctor_d₁ [HasZeroObject C₁] [DecidableEq I₁] (j : I₁) (A : C₁)
    (K : HomologicalComplex C₂ c₂) [HasMapBifunctor ((single C₁ c₁ j).obj A) K F c]
    (i₁ : I₁) (i₂ : I₂) (i : J) :
    mapBifunctor.d₁ ((single C₁ c₁ j).obj A) K F c i₁ i₂ i = 0 := by
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · by_cases h₂ : ComplexShape.π c₁ c₂ c (c₁.next i₁, i₂) = i
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
        NatTrans.app_zero, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]

/-- The second partial differential of `mapBifunctor K A[j] F c` vanishes, as the differential of
the single complex `A[j]` does. Mathlib's `HomologicalComplex.tensor_unit_d₂` is the case of the
tensor product with the monoidal unit in degree `0`; the proof is that of Mathlib's
`HomologicalComplex.tensor_unit_d₂`. -/
@[simp]
lemma mapBifunctor_single_d₂ [HasZeroObject C₂] [DecidableEq I₂] (j : I₂) (A : C₂)
    (K : HomologicalComplex C₁ c₁) [HasMapBifunctor K ((single C₂ c₂ j).obj A) F c]
    (i₁ : I₁) (i₂ : I₂) (i : J) :
    mapBifunctor.d₂ K ((single C₂ c₂ j).obj A) F c i₁ i₂ i = 0 := by
  by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
  · by_cases h₂ : ComplexShape.π c₁ c₂ c (i₁, c₂.next i₂) = i
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂, single_obj_d, Functor.map_zero, zero_comp,
        smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

end HomologicalComplex
