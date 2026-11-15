/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Two-term complexes and the triangle splitting off the top term

A short exact sequence or a conflation `X ⟶ Y ⟶ Z` is studied through the two-term complex
`Y ⟶ Z`. The chain map `X[0] ⟶ (Y ⟶ Z)` induced by `X ⟶ Y` is then a resolution of `X`, while
the degreewise split short exact sequence `Z[-1] ⟶ (Y ⟶ Z) ⟶ Y[0]` gives a distinguished
triangle of the homotopy category. Its third morphism is `Y ⟶ Z`, so its rotation, transported
along the resolution, is the triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` of the derived category.

The maps of two-term complexes are in `TauCeti/Algebra/Homology/HomologicalComplex/Double.lean`,
for any complex shape. This file treats the cohomological complex shape on `ℤ`: the connecting
morphism of the degreewise splitting of `X₁[i₁] ⟶ (X₀ ⟶ X₁) ⟶ X₀[i₀]` is `g`, and the short
complex `S : X ⟶ Y ⟶ Z` gives the two-term complex `S.double` in degrees `0` and `1`, which
receives `S.doubleι : X[0] ⟶ (Y ⟶ Z)`.

## Main definitions

* `CategoryTheory.ShortComplex.double` and `CategoryTheory.ShortComplex.doubleι`: for a short
  complex `X ⟶ Y ⟶ Z`, the two-term complex `Y ⟶ Z` in degrees `0` and `1`, and the chain map
  `X[0] ⟶ (Y ⟶ Z)` induced by `X ⟶ Y`.

## Main results

* `HomologicalComplex.homOfDegreewiseSplit_doubleSplitting_comp_shiftIso`: for cochain complexes
  indexed by `ℤ`, the connecting morphism of the split sequence `X₁[i₁] ⟶ (X₀ ⟶ X₁) ⟶ X₀[i₀]`
  is `g`.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

/-- Degrees `0` and `1` are adjacent for the cohomological complex shape on `ℤ`. -/
theorem ComplexShape.up_rel_zero_one : (ComplexShape.up ℤ).Rel 0 1 := by simp

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] {X₀ X₁ : C}
  (g : X₀ ⟶ X₁)

/-- **The connecting morphism of the split sequence `X₁[i₁] ⟶ (X₀ ⟶ X₁) ⟶ X₀[i₀]` is `g`**, up
to the identification `X₁[i₁][1] ≅ X₁[i₀]`. -/
theorem homOfDegreewiseSplit_doubleSplitting_comp_shiftIso {i₀ i₁ : ℤ}
    (hi₀₁ : (ComplexShape.up ℤ).Rel i₀ i₁) :
    CochainComplex.homOfDegreewiseSplit _
        (doubleSplitting g hi₀₁ fun e ↦ (ComplexShape.up ℤ).not_rel_of_eq e hi₀₁) ≫
      ((CochainComplex.singleFunctors C).shiftIso 1 i₀ i₁
        (by rw [ComplexShape.up_Rel] at hi₀₁; lia)).hom.app X₁ =
        (single C (.up ℤ) i₀).map g := by
  have h : i₀ ≠ i₁ := fun e ↦ (ComplexShape.up ℤ).not_rel_of_eq e hi₀₁
  obtain rfl : i₀ + 1 = i₁ := by rwa [ComplexShape.up_Rel] at hi₀₁
  apply from_single_hom_ext
  rw [comp_f, CochainComplex.homOfDegreewiseSplit_f, CochainComplex.cocycleOfDegreewiseSplit,
    CochainComplex.HomComplex.Cocycle.mk_coe, CochainComplex.HomComplex.Cochain.mk_v,
    doubleSplitting_s₀, doubleSplitting_r₁, double_d g hi₀₁ h, single_map_f_self]
  simp [CochainComplex.singleFunctors, singleObjXSelf, singleObjXIsoOfEq]

end HomologicalComplex

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C] (S : ShortComplex C)

/-- The two-term complex `Y ⟶ Z` of a short complex `X ⟶ Y ⟶ Z`, in degrees `0` and `1`. -/
noncomputable abbrev double : CochainComplex C ℤ :=
  HomologicalComplex.double S.g ComplexShape.up_rel_zero_one

/-- The chain map `X[0] ⟶ (Y ⟶ Z)` induced by `S.f` in degree `0`. -/
noncomputable def doubleι : (HomologicalComplex.single C (.up ℤ) 0).obj S.X₁ ⟶ S.double :=
  HomologicalComplex.mkHomFromSingle
    (S.f ≫ (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).inv)
    (by
      rintro k hk
      obtain rfl : k = 1 := (ComplexShape.up ℤ).next_eq hk ComplexShape.up_rel_zero_one
      simp [HomologicalComplex.double_d S.g ComplexShape.up_rel_zero_one zero_ne_one])

@[simp]
theorem doubleι_f_zero : S.doubleι.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom ≫ S.f ≫
      (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The chain map `X[0] ⟶ (Y ⟶ Z)` induced by `S.f`, followed by the projection onto `Y[0]`, is
`f`. -/
@[reassoc (attr := simp)]
theorem doubleι_doubleπ : S.doubleι ≫
    HomologicalComplex.doubleπ₀ S.g ComplexShape.up_rel_zero_one zero_ne_one =
      (HomologicalComplex.single C (.up ℤ) 0).map S.f := by
  apply HomologicalComplex.from_single_hom_ext
  simp [doubleι_f_zero, HomologicalComplex.doubleπ₀_f₀, HomologicalComplex.single_map_f_self]

/-- The chain map `X[0] ⟶ (Y ⟶ Z)` induced by `S.f` is natural in `S`. -/
@[reassoc (attr := simp)]
theorem doubleι_doubleMap {S' : ShortComplex C} (φ : S ⟶ S') :
    S.doubleι ≫ HomologicalComplex.doubleMap ComplexShape.up_rel_zero_one zero_ne_one φ.τ₂ φ.τ₃
      φ.comm₂₃ = (HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁ ≫ S'.doubleι := by
  apply HomologicalComplex.from_single_hom_ext
  simp [doubleι_f_zero, HomologicalComplex.single_map_f_self, reassoc_of% φ.comm₁₂]

end CategoryTheory.ShortComplex
