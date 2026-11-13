/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Exactness of a chain complex assembled from consecutive differentials

Translate exactness of consecutive pairs of specified differentials to `ExactAt` for
`ChainComplex.of`.
-/

public section

namespace ChainComplex

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Exactness of the specified differentials gives exactness in positive degrees of the
chain complex assembled by `ChainComplex.of`. -/
theorem of_exactAt_succ (X : ℕ → C) (d : ∀ n, X (n + 1) ⟶ X n)
    (zero : ∀ n, d (n + 1) ≫ d n = 0) (n : ℕ)
    (h : (ShortComplex.mk (d (n + 1)) (d n) (zero n)).Exact) :
    (ChainComplex.of X d zero).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  exact (ShortComplex.exact_iff_of_iso
    (S₁ := (ChainComplex.of X d zero).sc' (n + 1 + 1) (n + 1) n)
    (S₂ := ShortComplex.mk (d (n + 1)) (d n) (zero n))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa only [HomologicalComplex.shortComplexFunctor'_obj_f, Iso.refl_hom,
        Category.id_comp, Category.comp_id] using (ChainComplex.of_d X d (n + 1)).symm)
      (by simp))).2 h

/-- Exactness of the specified augmentation pair gives exactness at the augmentation of
`ChainComplex.of`. -/
theorem of_exact_d_one_zero (X : ℕ → C) (d : ∀ n, X (n + 1) ⟶ X n)
    (zero : ∀ n, d (n + 1) ≫ d n = 0) {Y : C} (ε : X 0 ⟶ Y)
    (hε : d 0 ≫ ε = 0) {hε' : (ChainComplex.of X d zero).d 1 0 ≫ ε = 0}
    (h : (ShortComplex.mk (d 0) ε hε).Exact) :
    (ShortComplex.mk ((ChainComplex.of X d zero).d 1 0) ε hε').Exact := by
  exact (ShortComplex.exact_iff_of_iso
    (S₁ := ShortComplex.mk ((ChainComplex.of X d zero).d 1 0) ε _)
    (S₂ := ShortComplex.mk (d 0) ε hε)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using (ChainComplex.of_d X d 0).symm) (by simp))).2 h

end ChainComplex
