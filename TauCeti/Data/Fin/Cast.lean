/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Casting finite indices

A family `x : ∀ i, Fin (f i) → α` of tuples of varying lengths is read at an index `a` through a
cast `Fin.cast ha : Fin n → Fin (f a)`. Equal indices `a = b` give equal readings, even though
`Fin (f a)` and `Fin (f b)` are not syntactically the same type, so the equation cannot be
rewritten directly.

Natural indices can also be read modulo the length of a nonempty finite ordinal. Rotating the
result advances the original natural index by one.

## Main results

* `Fin.apply_cast_eq_apply_cast`: reading `x` at equal indices through casts gives the same value.
* `Fin.finRotate_ofNat`: rotation commutes with taking the successor of a natural index.
-/

public section

namespace Fin

open Fin.NatCast in
/-- Rotation advances a natural index by one modulo the length. -/
theorem finRotate_ofNat {n : ℕ} [NeZero n] (i : ℕ) :
    finRotate n (Fin.ofNat n i) = Fin.ofNat n (i + 1) := by
  rw [finRotate_apply, Fin.ofNat_eq_cast, Fin.ofNat_eq_cast, Nat.cast_succ]

/-- Reading a family of tuples at equal indices, through casts of the coordinate to the lengths of
the tuples, gives the same value. -/
theorem apply_cast_eq_apply_cast {ι α : Type*} {f : ι → ℕ} (x : ∀ i, Fin (f i) → α) {a b : ι}
    (hab : a = b) {n : ℕ} (ha : n = f a) (hb : n = f b) (j : Fin n) :
    x a (Fin.cast ha j) = x b (Fin.cast hb j) := by
  subst hab
  -- The two casts now have the same source and target, so they agree by proof irrelevance.
  rfl

end Fin
