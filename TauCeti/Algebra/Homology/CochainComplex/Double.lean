/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# The two-term cochain complex of a short complex

For a short complex `S : X ⟶ Y ⟶ Z`, `S.double` is the cochain complex `Y ⟶ Z` in degrees `0`
and `1`. It receives `X` in degree `0` through `S.doubleι`, contains `Z` in degree `1` through
`S.doubleTopι`, and projects onto `Y` in degree `0` through `S.doubleπ`. The short complex
`Z[-1] ⟶ (Y ⟶ Z) ⟶ Y` is split in each degree, and its connecting morphism `Y[0] ⟶ Z[-1][1]`
is `g`, up to the identification `Z[-1][1] ≅ Z[0]`.

## Main definitions

* `CategoryTheory.ShortComplex.double`: the two-term complex `Y ⟶ Z`.
* `CategoryTheory.ShortComplex.doubleι`, `CategoryTheory.ShortComplex.doubleTopι` and
  `CategoryTheory.ShortComplex.doubleπ`: the maps `X[0] ⟶ (Y ⟶ Z)`, `Z[-1] ⟶ (Y ⟶ Z)` and
  `(Y ⟶ Z) ⟶ Y[0]`.
* `CategoryTheory.ShortComplex.doubleTopSplitting`: the degreewise splitting of
  `Z[-1] ⟶ (Y ⟶ Z) ⟶ Y[0]`.
* `CategoryTheory.ShortComplex.doubleMap`: the map of two-term complexes induced by a morphism of
  short complexes, with its components `doubleMap_f_zero` and `doubleMap_f_one`, functoriality
  `doubleMap_id` and `doubleMap_comp`, and naturality of `doubleι`, `doubleTopι` and `doubleπ`.

## Main results

* `CategoryTheory.ShortComplex.homOfDegreewiseSplit_doubleTopSplitting_comp_shiftIso`: the
  connecting morphism of the split sequence is `g`.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

/-- Degrees `0` and `1` are adjacent for the cohomological complex shape on `ℤ`. -/
theorem ComplexShape.up_rel_zero_one : (ComplexShape.up ℤ).Rel 0 1 := by simp

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] (S : ShortComplex C)

/-- The two-term complex `Y ⟶ Z` of a short complex `X ⟶ Y ⟶ Z`, in degrees `0` and `1`. -/
noncomputable abbrev double : CochainComplex C ℤ :=
  HomologicalComplex.double S.g ComplexShape.up_rel_zero_one

theorem isZero_double_X {m : ℤ} (h₀ : m ≠ 0) (h₁ : m ≠ 1) : IsZero (S.double.X m) :=
  HomologicalComplex.isZero_double_X _ _ _ h₀ h₁

/-- The inclusion of `X` in degree `0` into the two-term complex `Y ⟶ Z`. -/
noncomputable def doubleι : (HomologicalComplex.single C (.up ℤ) 0).obj S.X₁ ⟶ S.double :=
  HomologicalComplex.mkHomFromSingle
    (S.f ≫ (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).inv)
    (by
      rintro k (hk : 0 + 1 = k)
      obtain rfl : k = 1 := by lia
      rw [HomologicalComplex.double_d S.g ComplexShape.up_rel_zero_one (by simp)]
      simp)

theorem doubleι_f_zero : S.doubleι.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom ≫ S.f ≫
      (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The inclusion of the top term `Z`, in degree `1`, into the two-term complex `Y ⟶ Z`. -/
noncomputable def doubleTopι : (HomologicalComplex.single C (.up ℤ) 1).obj S.X₃ ⟶ S.double :=
  HomologicalComplex.mkHomFromSingle
    (HomologicalComplex.doubleXIso₁ S.g ComplexShape.up_rel_zero_one (by simp)).inv
    (by
      rintro k (hk : 1 + 1 = k)
      exact (S.isZero_double_X (by lia) (by lia)).eq_of_tgt _ _)

theorem doubleTopι_f_one : S.doubleTopι.f 1 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 1 S.X₃).hom ≫
      (HomologicalComplex.doubleXIso₁ S.g ComplexShape.up_rel_zero_one (by simp)).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The projection of the two-term complex `Y ⟶ Z` onto `Y` in degree `0`. -/
noncomputable def doubleπ : S.double ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj S.X₂ :=
  HomologicalComplex.mkHomFromDouble ComplexShape.up_rel_zero_one (by simp)
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₂).inv 0 (by simp) (by simp)

theorem doubleπ_f_zero : S.doubleπ.f 0 =
    (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₂).inv :=
  HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _

/-- The inclusion `X[0] ⟶ (Y ⟶ Z)` followed by the projection onto `Y[0]` is `f`. -/
@[reassoc (attr := simp)]
theorem doubleι_doubleπ :
    S.doubleι ≫ S.doubleπ = (HomologicalComplex.single C (.up ℤ) 0).map S.f := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, doubleι_f_zero, doubleπ_f_zero,
    HomologicalComplex.single_map_f_self]
  simp

instance : IsIso (S.doubleTopι.f 1) := by
  rw [doubleTopι_f_one]
  infer_instance

instance : IsIso (S.doubleπ.f 0) := by
  rw [doubleπ_f_zero]
  infer_instance

/-- The short complex `Z[-1] ⟶ (Y ⟶ Z) ⟶ Y[0]` splitting off the top term. -/
noncomputable abbrev doubleTopShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk S.doubleTopι S.doubleπ (by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    by_cases hn : n = 1
    · subst hn
      exact (HomologicalComplex.isZero_single_obj_X _ 0 _ 1 (by simp)).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ 1 _ n hn).eq_of_src _ _)

/-- The short complex `Z[-1] ⟶ (Y ⟶ Z) ⟶ Y[0]` is split in each degree. -/
noncomputable def doubleTopSplitting :
    ∀ n, (S.doubleTopShortComplex.map (HomologicalComplex.eval C _ n)).Splitting
  | Int.ofNat 0 => .ofIsZeroOfIsIso _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 S.X₃ (Int.ofNat 0) (by simp))
      (inferInstanceAs (IsIso (S.doubleπ.f 0)))
  | Int.ofNat 1 => .ofIsIsoOfIsZero _ (inferInstanceAs (IsIso (S.doubleTopι.f 1)))
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (Int.ofNat 1) (by simp))
  | Int.ofNat (k + 2) => .ofIsZeroOfIsIso _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 S.X₃ (Int.ofNat (k + 2)) (by lia))
      (isIso_of_source_target_iso_zero _ (S.isZero_double_X (by lia) (by lia)).isoZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (Int.ofNat (k + 2))
          (by lia)).isoZero)
  | Int.negSucc k => .ofIsZeroOfIsIso _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 S.X₃ (Int.negSucc k) (by lia))
      (isIso_of_source_target_iso_zero _ (S.isZero_double_X (by lia) (by lia)).isoZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (Int.negSucc k)
          (by lia)).isoZero)

/-- **The connecting morphism of the split sequence `Z[-1] ⟶ (Y ⟶ Z) ⟶ Y[0]` is `g`**, up to the
identification `Z[-1][1] ≅ Z[0]`. -/
theorem homOfDegreewiseSplit_doubleTopSplitting_comp_shiftIso :
    CochainComplex.homOfDegreewiseSplit _ S.doubleTopSplitting ≫
      ((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).hom.app S.X₃ =
        (HomologicalComplex.single C (.up ℤ) 0).map S.g := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, CochainComplex.homOfDegreewiseSplit_f]
  -- The cocycle of a degreewise splitting is, by definition, `s ≫ d ≫ r` for the sections and
  -- retractions of the splittings; in degree `0` these are the inverses of the isomorphisms
  -- `(doubleπ).f 0` and `(doubleTopι).f 1`.
  have h : (CochainComplex.cocycleOfDegreewiseSplit _ S.doubleTopSplitting).1.v 0 (0 + 1) rfl =
      inv (S.doubleπ.f 0) ≫ S.double.d 0 1 ≫ inv (S.doubleTopι.f 1) := rfl
  have h₁ : inv (S.doubleπ.f 0) = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₂).hom ≫
      (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).inv :=
    IsIso.inv_eq_of_hom_inv_id (by simp [doubleπ_f_zero])
  have h₂ : inv (S.doubleTopι.f 1) =
      (HomologicalComplex.doubleXIso₁ S.g ComplexShape.up_rel_zero_one (by simp)).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 1 S.X₃).inv :=
    IsIso.inv_eq_of_hom_inv_id (by simp [doubleTopι_f_one])
  rw [h, h₁, h₂, HomologicalComplex.double_d S.g ComplexShape.up_rel_zero_one (by simp),
    HomologicalComplex.single_map_f_self]
  simp [CochainComplex.singleFunctors, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

variable {S} {S' : ShortComplex C} (φ : S ⟶ S')

/-- The map of two-term complexes induced by a morphism of short complexes. -/
noncomputable def doubleMap : S.double ⟶ S'.double :=
  HomologicalComplex.mkHomFromDouble ComplexShape.up_rel_zero_one (by simp)
    (φ.τ₂ ≫ (HomologicalComplex.doubleXIso₀ S'.g ComplexShape.up_rel_zero_one).inv)
    (φ.τ₃ ≫ (HomologicalComplex.doubleXIso₁ S'.g ComplexShape.up_rel_zero_one (by simp)).inv)
    (by rw [HomologicalComplex.double_d S'.g ComplexShape.up_rel_zero_one (by simp)]
        simp [φ.comm₂₃])
    (by
      rintro k (hk : 1 + 1 = k)
      exact (S'.isZero_double_X (by lia) (by lia)).eq_of_tgt _ _)

/-- The degree-`0` component of `doubleMap φ` is `φ.τ₂`. -/
@[simp]
theorem doubleMap_f_zero : (doubleMap φ).f 0 =
    (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).hom ≫ φ.τ₂ ≫
      (HomologicalComplex.doubleXIso₀ S'.g ComplexShape.up_rel_zero_one).inv :=
  HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _

/-- The degree-`1` component of `doubleMap φ` is `φ.τ₃`. -/
@[simp]
theorem doubleMap_f_one : (doubleMap φ).f 1 =
    (HomologicalComplex.doubleXIso₁ S.g ComplexShape.up_rel_zero_one (by simp)).hom ≫ φ.τ₃ ≫
      (HomologicalComplex.doubleXIso₁ S'.g ComplexShape.up_rel_zero_one (by simp)).inv :=
  HomologicalComplex.mkHomFromDouble_f₁ _ _ _ _ _ _

variable (S) in
@[simp]
theorem doubleMap_id : doubleMap (𝟙 S) = 𝟙 S.double := by
  ext <;> simp

@[simp]
theorem doubleMap_comp {S'' : ShortComplex C} (ψ : S' ⟶ S'') :
    doubleMap (φ ≫ ψ) = doubleMap φ ≫ doubleMap ψ := by
  ext <;> simp

/-- The projection onto the degree-`0` term is natural. -/
@[reassoc (attr := simp)]
theorem doubleMap_doubleπ :
    doubleMap φ ≫ S'.doubleπ = S.doubleπ ≫ (HomologicalComplex.single C (.up ℤ) 0).map φ.τ₂ := by
  ext
  · simp [doubleπ_f_zero, HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _

@[reassoc (attr := simp)]
theorem doubleι_doubleMap :
    S.doubleι ≫ doubleMap φ = (HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁ ≫ S'.doubleι := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, doubleι_f_zero, doubleι_f_zero,
    HomologicalComplex.single_map_f_self, doubleMap, HomologicalComplex.mkHomFromDouble_f₀]
  simp [reassoc_of% φ.comm₁₂]

@[reassoc (attr := simp)]
theorem doubleTopι_doubleMap : S.doubleTopι ≫ doubleMap φ =
    (HomologicalComplex.single C (.up ℤ) 1).map φ.τ₃ ≫ S'.doubleTopι := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, doubleTopι_f_one, doubleTopι_f_one,
    HomologicalComplex.single_map_f_self, doubleMap, HomologicalComplex.mkHomFromDouble_f₁]
  simp

end CategoryTheory.ShortComplex
