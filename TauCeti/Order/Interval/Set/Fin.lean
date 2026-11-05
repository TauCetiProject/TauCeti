/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Unordered open intervals in `Fin n`

Membership in the unordered open interval `Set.uIoo a b` of `Fin n`, read off the values of the
points as natural numbers. Mathlib's `Fin.preimage_val_uIoo_val` identifies `Set.uIoo a b` with
the preimage of the corresponding interval of `ℕ`; `Fin.mem_uIoo_iff_val` unfolds this into two
strict inequalities against the minimum and maximum of the values of the endpoints, the form
consumed by `omega`.

## Main results

* `Fin.mem_uIoo_iff_val`: a point of `Fin n` lies strictly between `a` and `b` exactly when its
  value lies strictly between theirs.
-/

public section

namespace Fin

/-- A point of `Fin n` lies strictly between `a` and `b` exactly when its value lies strictly
between theirs. -/
theorem mem_uIoo_iff_val {n : ℕ} {a b x : Fin n} :
    x ∈ Set.uIoo a b ↔ min (a : ℕ) b < x ∧ (x : ℕ) < max (a : ℕ) b := by
  rw [← Set.Ioo_min_max, Set.mem_Ioo, Fin.lt_def, Fin.lt_def, Fin.val_min, Fin.val_max]

end Fin
