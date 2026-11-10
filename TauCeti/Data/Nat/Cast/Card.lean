/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finiteness from an invertible cardinality

A type whose cardinality is invertible in a nontrivial semiring is finite, since an infinite type
has `Nat.card` equal to `0`, and `0` is not invertible. This is how a finite-group hypothesis is
extracted from the condition that the order of the group is invertible in the coefficient ring.
-/

public section

namespace TauCeti

/-- A type whose cardinality is invertible in a nontrivial semiring is finite, since an infinite
type has cardinality `0`. -/
theorem finite_of_invertible_natCard {k : Type*} [Semiring k] [Nontrivial k] (G : Type*)
    [Invertible (Nat.card G : k)] : Finite G :=
  Nat.finite_of_card_ne_zero fun h ↦ Invertible.ne_zero (Nat.card G : k) (by simp [h])

end TauCeti
