/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Sign scaling of nonnegative or nonpositive elements

An element `x` of an ordered `R`-module satisfies `0 ≤ x ∨ x ≤ 0` if and only if some sign
`ε ∈ {1, -1}` in `R` satisfies `0 ≤ ε • x`. The same characterization holds for a dependent family
`v : ∀ i, M i` (all entries nonnegative or all entries nonpositive iff a common sign `ε ∈ {1, -1}`
makes every `ε • v i` nonnegative), and for left multiplication in a (not necessarily associative)
ring `R`.

## Main results

* `TauCeti.exists_eq_one_or_neg_one_and_smul_nonneg_iff`: characterization for an element of an
  ordered `R`-module.
* `TauCeti.exists_eq_one_or_neg_one_and_mul_nonneg_iff`: multiplication version for an element of
  a non-associative ring.
* `TauCeti.exists_eq_one_or_neg_one_and_forall_smul_nonneg_iff`: characterization for a dependent
  family of elements in ordered `R`-modules.
* `TauCeti.exists_eq_one_or_neg_one_and_forall_mul_nonneg_iff`: multiplication version for a
  ring-valued family.
-/

public section

namespace TauCeti

/-- An element `x` of an ordered `R`-module is nonnegative or nonpositive if and only if some sign
`ε ∈ {1, -1}` in `R` satisfies `0 ≤ ε • x`. -/
theorem exists_eq_one_or_neg_one_and_smul_nonneg_iff (R : Type*) {M : Type*} [Ring R]
    [AddCommGroup M] [LE M] [AddLeftMono M] [Module R M] (x : M) :
    (∃ ε : R, (ε = 1 ∨ ε = -1) ∧ 0 ≤ ε • x) ↔ 0 ≤ x ∨ x ≤ 0 := by
  simp only [or_and_right, exists_or, exists_eq_left, one_smul, neg_one_smul, neg_nonneg]

/-- An element `a` of an ordered non-associative ring `R` is nonnegative or nonpositive if and only
if some sign `ε ∈ {1, -1}` in `R` satisfies `0 ≤ ε * a`. -/
theorem exists_eq_one_or_neg_one_and_mul_nonneg_iff {R : Type*} [NonAssocRing R] [LE R]
    [AddLeftMono R] (a : R) :
    (∃ ε : R, (ε = 1 ∨ ε = -1) ∧ 0 ≤ ε * a) ↔ 0 ≤ a ∨ a ≤ 0 := by
  simp only [or_and_right, exists_or, exists_eq_left, one_mul, neg_one_mul, neg_nonneg]

/-- A dependent family `v : ∀ i, M i` of elements in ordered `R`-modules is pointwise nonnegative or
pointwise nonpositive if and only if some sign `ε ∈ {1, -1}` in `R` makes every `ε • v i`
nonnegative. -/
theorem exists_eq_one_or_neg_one_and_forall_smul_nonneg_iff (R : Type*) {ι : Type*}
    {M : ι → Type*} [Ring R] [∀ i, AddCommGroup (M i)] [∀ i, LE (M i)] [∀ i, AddLeftMono (M i)]
    [∀ i, Module R (M i)] (v : ∀ i, M i) :
    (∃ ε : R, (ε = 1 ∨ ε = -1) ∧ ∀ i, 0 ≤ ε • v i) ↔ (∀ i, 0 ≤ v i) ∨ ∀ i, v i ≤ 0 := by
  simp only [or_and_right, exists_or, exists_eq_left, one_smul, neg_one_smul, neg_nonneg]

/-- A family `v : ι → R` in an ordered non-associative ring `R` is pointwise nonnegative or
pointwise nonpositive if and only if some sign `ε ∈ {1, -1}` in `R` makes every `ε * v i`
nonnegative. -/
theorem exists_eq_one_or_neg_one_and_forall_mul_nonneg_iff {ι R : Type*} [NonAssocRing R] [LE R]
    [AddLeftMono R] (v : ι → R) :
    (∃ ε : R, (ε = 1 ∨ ε = -1) ∧ ∀ i, 0 ≤ ε * v i) ↔ (∀ i, 0 ≤ v i) ∨ ∀ i, v i ≤ 0 := by
  simp only [or_and_right, exists_or, exists_eq_left, one_mul, neg_one_mul, neg_nonneg]

end TauCeti
