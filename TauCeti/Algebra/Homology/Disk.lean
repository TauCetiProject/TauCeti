/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# The disk complex of an object

For an object `Q` of a category with zero morphisms and a zero object, the **disk** of `Q` is the
cochain complex `Q --𝟙--> Q` concentrated in degrees `-1` and `0`. It is acyclic, its terms are
projective when `Q` is, and its cycles in degree `0` are `Q`; so it is a complete resolution of a
projective object.

## Main definitions

* `CochainComplex.disk Q`: the complex `Q --𝟙--> Q` in degrees `-1` and `0`.
* `CochainComplex.diskCyclesIso Q`: the cycles of the disk in degree `0` are `Q`.

## Main results

* `CochainComplex.projective_disk_X`: the terms of the disk of a projective object are projective.
* `CochainComplex.disk_acyclic`: the disk is acyclic.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C] (Q : C)

/-- The relation `-1 → 0` in the shape of cochain complexes. -/
lemma up_rel_neg_one_zero : (ComplexShape.up ℤ).Rel (-1) 0 := by simp

/-- The **disk** of `Q`: the complex `Q --𝟙--> Q` concentrated in degrees `-1` and `0`. -/
noncomputable abbrev disk : CochainComplex C ℤ :=
  HomologicalComplex.double (𝟙 Q) up_rel_neg_one_zero

/-- The differential of the disk from degree `-1` to degree `0` is an isomorphism. -/
lemma isIso_disk_d : IsIso ((disk Q).d (-1) 0) := by
  rw [HomologicalComplex.double_d _ _ (by decide)]
  infer_instance

/-- The differentials of the disk out of degrees other than `-1` vanish. -/
lemma disk_d_eq_zero (j k : ℤ) (hj : j ≠ -1) : (disk Q).d j k = 0 :=
  HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hj

/-- The terms of the disk outside degrees `-1` and `0` are zero. -/
lemma isZero_disk_X (n : ℤ) (h₀ : n ≠ -1) (h₁ : n ≠ 0) : IsZero ((disk Q).X n) :=
  HomologicalComplex.isZero_double_X _ _ _ h₀ h₁

/-- The terms of the disk of a projective object are projective. -/
lemma projective_disk_X [Projective Q] (n : ℤ) : Projective ((disk Q).X n) := by
  by_cases h₀ : n = -1
  · subst h₀
    exact Projective.of_iso (HomologicalComplex.doubleXIso₀ (𝟙 Q) up_rel_neg_one_zero).symm
      inferInstance
  by_cases h₁ : n = 0
  · subst h₁
    exact Projective.of_iso
      (HomologicalComplex.doubleXIso₁ (𝟙 Q) up_rel_neg_one_zero (by decide)).symm inferInstance
  exact (isZero_disk_X Q n h₀ h₁).projective

/-- The cycles of the disk in degree `0` are `Q`. -/
noncomputable def diskCyclesIso [(disk Q).HasHomology 0] : (disk Q).cycles 0 ≅ Q :=
  (disk Q).iCyclesIso 0 1 (by simp) (disk_d_eq_zero Q _ _ (by decide)) ≪≫
    HomologicalComplex.doubleXIso₁ (𝟙 Q) up_rel_neg_one_zero (by decide)

end CochainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] (Q : C)

/-- The disk is acyclic. -/
lemma disk_acyclic : (disk Q).Acyclic := by
  have := isIso_disk_d Q
  intro n
  by_cases h₀ : n = -1
  · subst h₀
    rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
      ShortComplex.exact_iff_mono _ (disk_d_eq_zero Q _ _ (by decide))]
    exact inferInstanceAs (Mono ((disk Q).d (-1) 0))
  by_cases h₁ : n = 0
  · subst h₁
    rw [HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
      ShortComplex.exact_iff_epi _ (disk_d_eq_zero Q _ _ (by decide))]
    exact inferInstanceAs (Epi ((disk Q).d (-1) 0))
  exact HomologicalComplex.ExactAt.of_isZero (isZero_disk_X Q n h₀ h₁)

end CochainComplex
