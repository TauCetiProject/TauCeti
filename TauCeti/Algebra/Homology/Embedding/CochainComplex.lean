/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Data.Int.Interval

/-!
# Vanishing outside the bounds of a bounded cochain complex

Mathlib records the boundedness of a cochain complex indexed by `ℤ` in the classes
`CochainComplex.IsStrictlyGE` and `CochainComplex.IsStrictlyLE`, and converts them into vanishing
statements one strict inequality at a time. An argument that runs over the degrees of a bounded
complex instead wants the two bounds packaged as a single finite interval `Finset.Icc a b`, so
that membership in the summation range is the only case distinction left.

This file records the resulting two statements: outside `Finset.Icc a b` both the terms and the
cohomology of a complex strictly supported in `[a, b]` vanish. They are the finiteness input to
alternating-sum (Euler characteristic) computations over a bounded complex.

## Main results

* `HomologicalComplex.isZero_X_of_notMem_Icc`: the terms vanish outside the bounding interval.
* `HomologicalComplex.isZero_homology_of_notMem_Icc`: the cohomology vanishes outside the
  bounding interval.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- A strictly bounded cochain complex is zero outside any interval supplied by its bounds. -/
theorem isZero_X_of_notMem_Icc (K : CochainComplex A ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {n : ℤ} (hn : n ∉ Finset.Icc a b) : IsZero (K.X n) := by
  rw [Finset.mem_Icc] at hn
  rcases lt_or_ge n a with h | h
  · exact K.isZero_of_isStrictlyGE a n h
  · exact K.isZero_of_isStrictlyLE b n (by omega)

/-- The homology of a strictly bounded cochain complex is zero outside any interval supplied by
its bounds. -/
theorem isZero_homology_of_notMem_Icc (K : CochainComplex A ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {n : ℤ} [K.HasHomology n] (hn : n ∉ Finset.Icc a b) :
    IsZero (K.homology n) := by
  rw [Finset.mem_Icc] at hn
  rcases lt_or_ge n a with h | h
  · exact K.isZero_of_isGE a n h
  · exact K.isZero_of_isLE b n (by omega)

end HomologicalComplex
