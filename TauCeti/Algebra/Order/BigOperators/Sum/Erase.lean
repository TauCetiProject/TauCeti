/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Abs

/-!
# Absolute values of sums after merging two indices

Removing an index `t` from a finite sum and adding its value to the value at another index `t'`
can lower the sum of absolute values by at most the absolute value at `t`.

## Main results

* `Finset.sum_abs_erase_le`: `∑_{a ≠ t} |v a| ≤ ∑_{a ≠ t} |v a + [a = t'] v t| + |v t|`.
-/

public section

namespace Finset

/-- Merging the value at `t` into the value at another index `t'` costs `|v t|` once: the sum of
absolute values over the remaining indices is at most that of the merged values plus `|v t|`. -/
theorem sum_abs_erase_le {ι R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    [DecidableEq ι] {A : Finset ι} {t t' : ι} (ht'A' : t' ∈ A.erase t) (v : ι → R) :
    ∑ a ∈ A.erase t, |v a| ≤
      ∑ a ∈ A.erase t, |v a + if a = t' then v t else 0| + |v t| := by
  have hpt (a : ι) : |v a| ≤ |v a + if a = t' then v t else 0| + if a = t' then |v t| else 0 := by
    split_ifs with h
    · subst h
      simpa using abs_sub (v a + v t) (v t)
    · simp
  calc ∑ a ∈ A.erase t, |v a|
      ≤ ∑ a ∈ A.erase t, (|v a + if a = t' then v t else 0| + if a = t' then |v t| else 0) :=
        sum_le_sum fun a _ => hpt a
    _ = _ := by
      rw [sum_add_distrib, sum_ite_eq']
      simp [ht'A']

end Finset
