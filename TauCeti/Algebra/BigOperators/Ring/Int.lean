/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Int.Units

/-!
# Finite products of integer signs

A finite product of integers taking values in `{-1, 1}` differs from `1` exactly when
it equals `-1`. The statement includes the empty product and imposes sign hypotheses
only on the factors in the indexing finset.
-/

public section

namespace Int

/-- A finite product of integer signs differs from `1` exactly when it equals `-1`. -/
theorem prod_ne_one_iff_eq_neg_one {ι : Type*} {s : Finset ι} {f : ι → ℤ}
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) ≠ 1 ↔ (∏ i ∈ s, f i) = -1 :=
  isUnit_ne_iff_eq_neg
    (IsUnit.prod_iff.mpr fun i hi ↦ isUnit_iff.mpr (hf i hi)) isUnit_one

end Int
