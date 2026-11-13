/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Maps of two-term complexes

For a morphism `g : X₀ ⟶ X₁` and adjacent degrees `i₀ ≠ i₁` of a complex shape `c`, Mathlib's
`HomologicalComplex.double g hi₀₁` is the two-term complex `X₀ ⟶ X₁`. This file provides the
inclusion of `X₁` in degree `i₁`, the projection onto `X₀` in degree `i₀`, the degreewise
splitting of the short complex `X₁[i₁] ⟶ (X₀ ⟶ X₁) ⟶ X₀[i₀]` they form, and the map of two-term
complexes induced by a commutative square. Nothing depends on the shape `c`.

The structural maps and `HomologicalComplex.doubleMap` need zero morphisms and a zero object; the
degreewise splitting needs a preadditive category with a zero object.

## Main definitions

* `HomologicalComplex.doubleι₁` and `HomologicalComplex.doubleπ₀`: the maps
  `X₁[i₁] ⟶ (X₀ ⟶ X₁)` and `(X₀ ⟶ X₁) ⟶ X₀[i₀]`.
* `HomologicalComplex.doubleShortComplex`: the short complex `X₁[i₁] ⟶ (X₀ ⟶ X₁) ⟶ X₀[i₀]`.
* `HomologicalComplex.doubleSplitting`: its degreewise splitting.
* `HomologicalComplex.doubleMap`: the map of two-term complexes induced by a commutative square,
  with its components `doubleMap_f₀` and `doubleMap_f₁`, functoriality `doubleMap_id` and
  `doubleMap_comp`, and naturality of `doubleι₁` and `doubleπ₀`.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

namespace HomologicalComplex

section ZeroMorphisms

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {X₀ X₁ : C} {g : X₀ ⟶ X₁} {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι}
  (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁)
  {Y₀ Y₁ : C} {g' : Y₀ ⟶ Y₁} (τ₀ : X₀ ⟶ Y₀) (τ₁ : X₁ ⟶ Y₁) (comm : τ₀ ≫ g' = g ≫ τ₁)

/-- The map of two-term complexes `(X₀ ⟶ X₁) ⟶ (Y₀ ⟶ Y₁)` induced by a commutative square. -/
noncomputable def doubleMap : double g hi₀₁ ⟶ double g' hi₀₁ :=
  mkHomFromDouble hi₀₁ h (τ₀ ≫ (doubleXIso₀ g' hi₀₁).inv) (τ₁ ≫ (doubleXIso₁ g' hi₀₁ h).inv)
    (by simp [double_d g' hi₀₁ h, reassoc_of% comm])
    (fun k _ ↦ by rw [double_d_eq_zero₀ g' hi₀₁ _ _ h.symm, comp_zero])

/-- The degree-`i₀` component of `doubleMap` is `τ₀`. -/
@[simp]
theorem doubleMap_f₀ : (doubleMap hi₀₁ h τ₀ τ₁ comm).f i₀ =
    (doubleXIso₀ g hi₀₁).hom ≫ τ₀ ≫ (doubleXIso₀ g' hi₀₁).inv :=
  mkHomFromDouble_f₀ _ _ _ _ _ _

/-- The degree-`i₁` component of `doubleMap` is `τ₁`. -/
@[simp]
theorem doubleMap_f₁ : (doubleMap hi₀₁ h τ₀ τ₁ comm).f i₁ =
    (doubleXIso₁ g hi₀₁ h).hom ≫ τ₁ ≫ (doubleXIso₁ g' hi₀₁ h).inv :=
  mkHomFromDouble_f₁ _ _ _ _ _ _

variable (g) in
@[simp]
theorem doubleMap_id : doubleMap hi₀₁ h (𝟙 X₀) (𝟙 X₁) (by simp) = 𝟙 (double g hi₀₁) := by
  ext <;> simp

theorem doubleMap_comp {Z₀ Z₁ : C} {g'' : Z₀ ⟶ Z₁} (σ₀ : Y₀ ⟶ Z₀) (σ₁ : Y₁ ⟶ Z₁)
    (comm' : σ₀ ≫ g'' = g' ≫ σ₁) :
    doubleMap hi₀₁ h (τ₀ ≫ σ₀) (τ₁ ≫ σ₁) (by simp [comm', reassoc_of% comm]) =
      doubleMap hi₀₁ h τ₀ τ₁ comm ≫ doubleMap hi₀₁ h σ₀ σ₁ comm' := by
  ext <;> simp

variable (g) [DecidableEq ι]

/-- The inclusion of `X₁`, in degree `i₁`, into the two-term complex `X₀ ⟶ X₁`. -/
noncomputable def doubleι₁ : (single C c i₁).obj X₁ ⟶ double g hi₀₁ :=
  mkHomFromSingle (doubleXIso₁ g hi₀₁ h).inv fun k _ ↦ by
    rw [double_d_eq_zero₀ g hi₀₁ _ _ h.symm, comp_zero]

theorem doubleι₁_f₁ : (doubleι₁ g hi₀₁ h).f i₁ =
    (singleObjXSelf c i₁ X₁).hom ≫ (doubleXIso₁ g hi₀₁ h).inv :=
  mkHomFromSingle_f _ _

instance : IsIso ((doubleι₁ g hi₀₁ h).f i₁) := by
  rw [doubleι₁_f₁]
  infer_instance

/-- The projection of the two-term complex `X₀ ⟶ X₁` onto `X₀`, in degree `i₀`. -/
noncomputable def doubleπ₀ : double g hi₀₁ ⟶ (single C c i₀).obj X₀ :=
  mkHomFromDouble hi₀₁ h (singleObjXSelf c i₀ X₀).inv 0 (by simp [single_obj_d]) (by simp)

theorem doubleπ₀_f₀ : (doubleπ₀ g hi₀₁ h).f i₀ =
    (doubleXIso₀ g hi₀₁).hom ≫ (singleObjXSelf c i₀ X₀).inv :=
  mkHomFromDouble_f₀ _ _ _ _ _ _

instance : IsIso ((doubleπ₀ g hi₀₁ h).f i₀) := by
  rw [doubleπ₀_f₀]
  infer_instance

/-- The short complex `X₁[i₁] ⟶ (X₀ ⟶ X₁) ⟶ X₀[i₀]` splitting off the term in degree `i₁`. -/
noncomputable abbrev doubleShortComplex : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (doubleι₁ g hi₀₁ h) (doubleπ₀ g hi₀₁ h)
    (from_single_hom_ext ((isZero_single_obj_X c i₀ X₀ i₁ h.symm).eq_of_tgt _ _))

variable {g}

/-- The projection onto the degree-`i₀` term is natural. -/
@[reassoc (attr := simp)]
theorem doubleMap_doubleπ₀ : doubleMap hi₀₁ h τ₀ τ₁ comm ≫ doubleπ₀ g' hi₀₁ h =
    doubleπ₀ g hi₀₁ h ≫ (single C c i₀).map τ₀ := by
  ext
  · simp [doubleπ₀_f₀, single_map_f_self]
  · exact (isZero_single_obj_X c i₀ Y₀ i₁ h.symm).eq_of_tgt _ _

/-- The inclusion of the degree-`i₁` term is natural. -/
@[reassoc (attr := simp)]
theorem doubleι₁_doubleMap : doubleι₁ g hi₀₁ h ≫ doubleMap hi₀₁ h τ₀ τ₁ comm =
    (single C c i₁).map τ₁ ≫ doubleι₁ g' hi₀₁ h := by
  apply from_single_hom_ext
  simp [doubleι₁_f₁, single_map_f_self]

end ZeroMorphisms

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {X₀ X₁ : C} (g : X₀ ⟶ X₁) {ι : Type*} [DecidableEq ι] {c : ComplexShape ι} {i₀ i₁ : ι}
  (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁)

/-- The short complex `X₁[i₁] ⟶ (X₀ ⟶ X₁) ⟶ X₀[i₀]` is split in each degree. -/
noncomputable def doubleSplitting (n : ι) :
    ((doubleShortComplex g hi₀₁ h).map (eval C c n)).Splitting :=
  if hn₀ : n = i₀ then
    .ofIsZeroOfIsIso _ (isZero_single_obj_X c i₁ X₁ n (hn₀.trans_ne h))
      (by subst hn₀; exact inferInstanceAs (IsIso ((doubleπ₀ g hi₀₁ h).f n)))
  else if hn₁ : n = i₁ then
    .ofIsIsoOfIsZero _ (by subst hn₁; exact inferInstanceAs (IsIso ((doubleι₁ g hi₀₁ h).f n)))
      (isZero_single_obj_X c i₀ X₀ n hn₀)
  else
    .ofIsZeroOfIsIso _ (isZero_single_obj_X c i₁ X₁ n hn₁)
      (isIso_of_source_target_iso_zero _ (isZero_double_X g hi₀₁ n hn₀ hn₁).isoZero
        (isZero_single_obj_X c i₀ X₀ n hn₀).isoZero)

/-- In degree `i₀`, the section of the splitting inverts the projection onto `X₀`. -/
theorem doubleSplitting_s₀ : (doubleSplitting g hi₀₁ h i₀).s =
    (singleObjXSelf c i₀ X₀).hom ≫ (doubleXIso₀ g hi₀₁).inv := by
  rw [← cancel_mono ((doubleπ₀ g hi₀₁ h).f i₀)]
  simpa [doubleπ₀_f₀] using (doubleSplitting g hi₀₁ h i₀).s_g

/-- In degree `i₁`, the retraction of the splitting inverts the inclusion of `X₁`. -/
theorem doubleSplitting_r₁ : (doubleSplitting g hi₀₁ h i₁).r =
    (doubleXIso₁ g hi₀₁ h).hom ≫ (singleObjXSelf c i₁ X₁).inv := by
  rw [← cancel_epi ((doubleι₁ g hi₀₁ h).f i₁)]
  simpa [doubleι₁_f₁] using (doubleSplitting g hi₀₁ h i₁).f_r

end Preadditive

end HomologicalComplex
