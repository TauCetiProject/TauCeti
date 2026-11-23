/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Basic

/-!
# Reading families of tuples through casts of the index

A family `x : ∀ i, Fin (f i) → α` of tuples of varying lengths is read at an index `a` through a
cast `Fin.cast ha : Fin n → Fin (f a)`. Equal indices `a = b` give equal readings, even though
`Fin (f a)` and `Fin (f b)` are not syntactically the same type, so the equation cannot be
rewritten directly.

## Main results

* `Fin.apply_cast_eq_apply_cast`: reading `x` at equal indices through casts gives the same value.
-/

public section

namespace Fin

/-- Reading a family of tuples at equal indices, through casts of the coordinate to the lengths of
the tuples, gives the same value. -/
theorem apply_cast_eq_apply_cast {ι α : Sort*} {f : ι → ℕ} (x : ∀ i, Fin (f i) → α) {a b : ι}
    (hab : a = b) {n : ℕ} (ha : n = f a) (hb : n = f b) (j : Fin n) :
    x a (Fin.cast ha j) = x b (Fin.cast hb j) := by
  subst hab
  -- The two casts now have the same source and target, so they agree by proof irrelevance.
  rfl

end Fin
