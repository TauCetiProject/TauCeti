/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import TauCeti.NumberTheory.EffectiveBounds.QuadraticClassNumber

/-!
# Worked examples: the effective bounds on the named quadratic fields

The effective-bounds roadmap keeps its estimates honest with two arithmetic worked examples,
each asking that a general bound be exercised on a *named* number field rather than a
same-shape analogue:

* the cyclotomic discriminant formula gives `|d_{ℚ(i)}| = 4`;
* the class-number bound is non-vacuous on `ℚ(√-5)`, giving `h ≤ 64·5`.

This file realises both on concrete `NumberField` instances.

For `ℚ(√-5)` we take `AdjoinRoot (X² + 5)` over `ℚ` (a field because `X² + 5` is irreducible,
having no rational root), a degree-two number field with a square root of `-5`, and feed it to
`TauCeti.NumberField.classNumber_le_natAbs_of_sq_intCast`.

For `ℚ(i)` we take the fourth cyclotomic field `CyclotomicField 4 ℚ` and specialize Mathlib's
prime-power cyclotomic discriminant formula, giving `d_{ℚ(i)} = -4` and hence
`|d_{ℚ(i)}| = 4`.

## Main results

* `TauCeti.NumberField.WorkedExamples.classNumber_adjoinRoot_sqrt_neg_five_le`: `h ≤ 320` for
  `ℚ(√-5)`.
* `TauCeti.NumberField.WorkedExamples.discr_cyclotomicField_four`: `d_{ℚ(i)} = -4`.
* `TauCeti.NumberField.WorkedExamples.natAbs_discr_cyclotomicField_four`: `|d_{ℚ(i)}| = 4`.

## Provenance

No formal code is vendored. The effective bounds consumed here (`classNumber_le_bound` and the
quadratic corollary) carry their own attribution to `kim-em/erdos-unit-distance`; the
`NumberField` construction for `ℚ(√-5)` and the arithmetic specialisations are new.
-/

public section

open Polynomial Module
open scoped NumberField

namespace TauCeti.NumberField.WorkedExamples

/-! ### `ℚ(√-5)`: the class-number bound is non-vacuous -/

/-- `X² + 5` is irreducible over `ℚ`: a monic quadratic with no rational root (a rational
square is nonnegative, but `-5 < 0`). -/
instance : Fact (Irreducible (X ^ 2 - C (-5 : ℚ))) := ⟨by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_sub_C]; decide
  · intro x hx
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hx
    nlinarith [sq_nonneg x]⟩

/-- **The class-number bound on `ℚ(√-5)`.** The class number of `ℚ(√-5)`, modelled as
`AdjoinRoot (X² + 5)`, is at most `64·5 = 320`; this is the roadmap's non-vacuity worked
example for the effective class-number bound. -/
theorem classNumber_adjoinRoot_sqrt_neg_five_le :
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (-5 : ℚ))) ≤ 320 := by
  set f : ℚ[X] := X ^ 2 - C (-5 : ℚ) with hf
  have hfne : f ≠ 0 := (monic_X_pow_sub_C _ (two_ne_zero)).ne_zero
  -- `[K : ℚ] = 2`.
  have hfin : finrank ℚ (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hfne).finrank, AdjoinRoot.powerBasis_dim hfne, hf,
      natDegree_X_pow_sub_C]
  -- The image of `AdjoinRoot.root f` is a square root of `-5`.
  have hx2 : (AdjoinRoot.root f) ^ 2 = algebraMap ℤ (AdjoinRoot f) (-5 : ℤ) := by
    have hroot := AdjoinRoot.eval₂_root f
    rw [hf, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ← AdjoinRoot.algebraMap_eq, sub_eq_zero]
      at hroot
    rw [hroot, IsScalarTower.algebraMap_apply ℤ ℚ (AdjoinRoot f)]
    norm_num
  -- The root is not rational: else `-5` would be a rational square.
  have hx : AdjoinRoot.root f ∉ (algebraMap ℚ (AdjoinRoot f)).range := by
    rintro ⟨q, hq⟩
    have h1 : algebraMap ℚ (AdjoinRoot f) (q ^ 2) = algebraMap ℚ (AdjoinRoot f) (-5 : ℚ) := by
      rw [map_pow, hq, hx2, IsScalarTower.algebraMap_apply ℤ ℚ (AdjoinRoot f)]; norm_num
    nlinarith [sq_nonneg q, (algebraMap ℚ (AdjoinRoot f)).injective h1]
  have := classNumber_le_natAbs_of_sq_intCast hfin hx2 hx
  simpa using this

/-! ### `ℚ(i)`: Mathlib's cyclotomic discriminant formula recovers `|d| = 4` -/

/-- **The discriminant of `ℚ(i)`.** Mathlib's cyclotomic discriminant formula gives
`d_{ℚ(i)} = -4` for the fourth cyclotomic field, which is the roadmap's exact-discriminant
worked example. -/
@[simp]
theorem discr_cyclotomicField_four : NumberField.discr (CyclotomicField 4 ℚ) = -4 := by
  haveI : IsCyclotomicExtension {2 ^ (1 + 1)} ℚ (CyclotomicField 4 ℚ) := by
    have h : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
      CyclotomicField.isCyclotomicExtension 4 ℚ
    simpa using h
  rw [IsCyclotomicExtension.Rat.discr_prime_pow_succ (p := 2) (k := 1)
    (K := CyclotomicField 4 ℚ)]
  norm_num

/-- **The absolute discriminant of `ℚ(i)`.** The fourth cyclotomic field has absolute
discriminant `4`, obtained from the signed discriminant worked example. -/
theorem natAbs_discr_cyclotomicField_four :
    (NumberField.discr (CyclotomicField 4 ℚ)).natAbs = 4 := by
  rw [discr_cyclotomicField_four]
  norm_num

end TauCeti.NumberField.WorkedExamples
