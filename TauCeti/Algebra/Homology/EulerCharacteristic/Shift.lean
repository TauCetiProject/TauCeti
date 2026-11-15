/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Euler characteristics of shifted cochain complexes

The term of the shifted cochain complex `K⟦a⟧` in degree `i` is the term of `K` in degree `i + a`,
so shifting by `a` moves every term across `a` degrees and multiplies the Euler characteristic of
the terms by `(-1) ^ a`. This is the bookkeeping needed when a complex is built in one grading and
normalized by a shift, as for the normalized Khovanov complex.

The identity holds for Mathlib's `finsum`-based definition without any finiteness hypothesis:
reindexing preserves the support of the summand, and multiplication by the unit `(-1) ^ a` of `ℤ`
does not change it either.

## Main results

* `CochainComplex.eulerChar_shift`: `χ(K⟦a⟧) = (-1) ^ a χ(K)`.
-/

public section

open CategoryTheory

universe u v

namespace CochainComplex

variable {R : Type u} [Ring R]

/-- Shifting a cochain complex of modules by `a` multiplies the Euler characteristic of its terms
by `(-1) ^ a`. -/
@[simp]
theorem eulerChar_shift (K : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ) :
    (K⟦a⟧).eulerChar = a.negOnePow * K.eulerChar := by
  -- Reindex the sum by `i ↦ i + a`; the sign `(-1) ^ i` becomes `(-1) ^ (j - a)`.
  let g : ℤ → ℤ := fun j ↦ (j - a).negOnePow * Module.finrank R (K.X j)
  calc (K⟦a⟧).eulerChar = ∑ᶠ i : ℤ, g (Equiv.addRight a i) :=
        finsum_congr fun i ↦ by simp [g]
    _ = ∑ᶠ j : ℤ, g j := finsum_comp_equiv (Equiv.addRight a)
    _ = a.negOnePow * K.eulerChar := by
        rw [HomologicalComplex.eulerChar, GradedObject.eulerChar, mul_finsum]
        refine finsum_congr fun j ↦ ?_
        simp only [g, Int.negOnePow_sub, ComplexShape.eulerCharSignsUpInt_χ, Units.val_mul]
        rw [mul_comm (j.negOnePow : ℤ), mul_assoc]

end CochainComplex
