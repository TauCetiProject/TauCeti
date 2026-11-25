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
# Sign scaling of nonnegative or nonpositive families

A dependent family `v : ∀ i, M i` of elements in ordered `R`-modules has all entries nonnegative or
all entries nonpositive (`(∀ i, 0 ≤ v i) ∨ ∀ i, v i ≤ 0`) if and only if some common sign
`ε ∈ {1, -1}` in `R` makes every `ε • v i` nonnegative.

## Main results

* `TauCeti.exists_eq_one_or_neg_one_and_forall_smul_nonneg_iff`: characterization for a dependent
  family of elements in ordered `R`-modules.
-/

public section

namespace TauCeti

/-- A dependent family `v : ∀ i, M i` of elements in ordered `R`-modules is pointwise nonnegative or
pointwise nonpositive if and only if some sign `ε ∈ {1, -1}` in `R` makes every `ε • v i`
nonnegative. -/
theorem exists_eq_one_or_neg_one_and_forall_smul_nonneg_iff (R : Type*) {ι : Type*}
    {M : ι → Type*} [Ring R] [∀ i, AddCommGroup (M i)] [∀ i, LE (M i)] [∀ i, AddLeftMono (M i)]
    [∀ i, Module R (M i)] (v : ∀ i, M i) :
    (∃ ε : R, (ε = 1 ∨ ε = -1) ∧ ∀ i, 0 ≤ ε • v i) ↔ (∀ i, 0 ≤ v i) ∨ ∀ i, v i ≤ 0 := by
  simp only [or_and_right, exists_or, exists_eq_left, one_smul, neg_one_smul, neg_nonneg]

end TauCeti
