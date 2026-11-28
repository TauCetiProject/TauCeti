/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Divisible
public import TauCeti.GroupTheory.Divisible.Units

/-!
# Divisibility of the units of an algebraically closed field

Every unit of an algebraically closed field has an `n`-th root for each nonzero natural
number `n`, in every characteristic. The resulting rootability instance allows the additive
type tag of the unit group to be used as a divisible group, for example to extend characters
from subgroups by Baer's criterion.
-/

public section

namespace TauCeti.IsAlgClosed

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- The unit group of an algebraically closed field is divisible. -/
noncomputable instance unitsRootableByNat : RootableBy kˣ ℕ :=
  unitsRootableByNatOfExistsPow fun _ hn a ↦
    IsAlgClosed.exists_pow_nat_eq (a : k) (Nat.pos_of_ne_zero hn)

end TauCeti.IsAlgClosed
