/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Basis

/-!
# Commutators of matrix units

This file computes brackets of single-entry matrices over an arbitrary ring. The basic
`Matrix.lie_single_single` formula gives the two possible compositions of matrix units. Its
specializations express off-diagonal units and diagonal differences as commutators, and compute
their brackets used in standard `sl₂` triples. The double-bracket identity
`Matrix.lie_single_lie_single_of_ne` extracts one matrix entry, which is useful for studying
ideals of matrix Lie algebras.

These identities concern the underlying Lie ring, so they do not require commutative coefficients
or a choice of scalar ring for a Lie algebra.
-/

public section

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [Ring R] {n : Type*} [DecidableEq n] [Fintype n]

/-- The commutator of two single-entry matrices is the difference of the two possible
composites. -/
@[simp]
theorem lie_single_single (a b i j : n) (c d : R) :
    ⁅single a b c, single i j d⁆ =
      (if b = i then single a j (c * d) else 0) -
        if j = a then single i b (d * c) else 0 := by
  rw [LieRing.of_associative_ring_bracket]
  by_cases hbi : b = i
  · subst i
    by_cases hja : j = a
    · subst j
      rw [single_mul_single_same, single_mul_single_same]
      simp
    · rw [single_mul_single_same, single_mul_single_of_ne (h := hja)]
      simp [hja]
  · by_cases hja : j = a
    · subst j
      rw [single_mul_single_of_ne (h := hbi), single_mul_single_same]
      simp [hbi]
    · rw [single_mul_single_of_ne (h := hbi), single_mul_single_of_ne (h := hja)]
      simp [hbi, hja]

/-- An off-diagonal matrix unit is a commutator: `Eᵢⱼ = ⁅Eᵢᵢ, Eᵢⱼ⁆` when `i ≠ j`. -/
theorem lie_single_self_single_of_ne {i j : n} (hij : i ≠ j) (c : R) :
    ⁅single i i (1 : R), single i j c⁆ = single i j c := by
  rw [LieRing.of_associative_ring_bracket, single_mul_single_same,
    single_mul_single_of_ne (h := Ne.symm hij), one_mul, sub_zero]

/-- A difference of diagonal matrix units is a commutator: `Eᵢᵢ - Eⱼⱼ = ⁅Eᵢⱼ, Eⱼᵢ⁆`. -/
theorem lie_single_single_eq_sub (i j : n) (c : R) :
    ⁅single i j c, single j i (1 : R)⁆ = single i i c - single j j c := by
  rw [LieRing.of_associative_ring_bracket, single_mul_single_same, single_mul_single_same, mul_one,
    one_mul]

/-- A difference of diagonal matrix units doubles the matrix unit between them. -/
theorem lie_single_self_sub_single_self_single {p q : n} (hpq : p ≠ q) (c : R) :
    ⁅single p p (1 : R) - single q q (1 : R), single p q c⁆ = single p q (2 * c) := by
  simp [sub_lie, lie_single_single, hpq.symm, two_mul, single_add]

/-- Bracketing twice against an off-diagonal matrix unit isolates the transposed entry. -/
theorem lie_single_lie_single_of_ne {i j : n} (hij : i ≠ j) (x : Matrix n n R) :
    ⁅single j i (1 : R), ⁅single j i (1 : R), x⁆⁆ = single j i (-(2 * x i j)) := by
  have hsq : single j i (1 : R) * single j i (1 : R) = 0 := by
    rw [single_mul_single_of_ne (h := hij)]
  have hmid : single j i (1 : R) * x * single j i (1 : R) = single j i (x i j) := by
    simp [single_mul_mul_single]
  simp only [LieRing.of_associative_ring_bracket, mul_sub, sub_mul, ← mul_assoc,
    hsq, zero_mul, hmid, zero_sub]
  rw [mul_assoc x, hsq]
  simp [two_mul, single_add, single_neg, sub_eq_add_neg]

end Matrix
