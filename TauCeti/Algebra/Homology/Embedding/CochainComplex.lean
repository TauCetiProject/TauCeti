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

This file records the resulting two statements: outside `Finset.Icc a b`, the terms of a strictly
bounded complex vanish, while its cohomology vanishes under the corresponding cohomological
bounds. They are the finiteness input to alternating-sum (Euler characteristic) computations over
a bounded complex. It also records that the canonical truncation `K.truncGE a` keeps an upper
bound of `K`.

## Main results

* `CochainComplex.isZero_X_of_notMem_Icc`: the terms vanish outside the bounding interval.
* `CochainComplex.isZero_homology_of_notMem_Icc`: the cohomology vanishes outside the
  bounding interval.
* `CochainComplex.isStrictlyLE_truncGE`: the truncation `K.truncGE a` is strictly bounded above
  by any strict upper bound of `K`.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- A strictly bounded cochain complex is zero outside any interval supplied by its bounds. -/
theorem isZero_X_of_notMem_Icc (K : CochainComplex A ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {n : ℤ} (hn : n ∉ Finset.Icc a b) : IsZero (K.X n) := by
  obtain h | h : n < a ∨ b < n := by simp only [Finset.mem_Icc] at hn; omega
  exacts [K.isZero_of_isStrictlyGE a n h, K.isZero_of_isStrictlyLE b n h]

/-- The homology of a cochain complex is zero outside any interval supplied by its cohomological
bounds. -/
theorem isZero_homology_of_notMem_Icc (K : CochainComplex A ℤ) (a b : ℤ) [K.IsGE a]
    [K.IsLE b] {n : ℤ} [K.HasHomology n] (hn : n ∉ Finset.Icc a b) :
    IsZero (K.homology n) := by
  obtain h | h : n < a ∨ b < n := by simp only [Finset.mem_Icc] at hn; omega
  exacts [K.isZero_of_isGE a n h, K.isZero_of_isLE b n h]

/-- The canonical truncation `K.truncGE a` of a complex strictly bounded above by `b` is still
strictly bounded above by `b`: its terms are those of `K` in degrees `> a`, a quotient of `K.X a`
in degree `a`, and zero below. -/
instance isStrictlyLE_truncGE [HasZeroObject A] (K : CochainComplex A ℤ) [∀ i, K.HasHomology i]
    (a b : ℤ) [K.IsStrictlyLE b] : (K.truncGE a).IsStrictlyLE b := by
  rw [isStrictlyLE_iff]
  intro i hi
  rcases lt_trichotomy a i with h | rfl | h
  · exact (K.isZero_of_isStrictlyLE b i).of_iso (K.truncGEXIso a i)
  · exact ((K.isZero_of_isStrictlyLE b a).of_epi (K.pOpcycles a)).of_iso
      (K.truncGEXIsoOpcycles a)
  · exact (K.truncGE a).isZero_of_isStrictlyGE a i

end CochainComplex
