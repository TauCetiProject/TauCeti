/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.GCD.Basic

/-!
# Coprime cardinalities with an infinite type

The cardinality `Nat.card` of an infinite type is `0`, and `0` is coprime only to `1`. Hence a type
whose cardinality is coprime to that of an infinite type has exactly one element.

## Main results

* `Nat.subsingleton_of_coprime_card_of_infinite`: if `Nat.card α` and `Nat.card β` are coprime and
  `α` is infinite, then `β` is a subsingleton.
-/

public section

namespace Nat

/-- If the cardinalities of `α` and `β` are coprime and `α` is infinite (so that `Nat.card α = 0`),
then `β` has exactly one element, in particular it is a subsingleton. -/
theorem subsingleton_of_coprime_card_of_infinite {α β : Type*} [Infinite α]
    (h : (Nat.card α).Coprime (Nat.card β)) : Subsingleton β := by
  rw [Nat.card_eq_zero_of_infinite, Nat.coprime_zero_left] at h
  exact (Nat.card_eq_one_iff_unique.mp h).1

end Nat
