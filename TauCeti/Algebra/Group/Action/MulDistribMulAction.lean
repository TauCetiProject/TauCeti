/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# A multiplicative action on a monoid is distributive over its self-action

A multiplicative distributive action of `G` on a monoid `A`, such as a `MulSemiringAction`, has
`g • (a * b) = g • a * g • b`. Read with `A` acting on itself by left multiplication, this is
`SMulDistribClass G A A`, the form taken by statements about semilinear actions on `A`-modules
when the module is `A` itself.

## Main results

* `TauCeti.smulDistribClass_self`: `SMulDistribClass G A A` for a `MulDistribMulAction G A`.
-/

public section

namespace TauCeti

/-- A multiplicative distributive action of `G` on a monoid `A` distributes over the action of `A`
on itself by left multiplication. -/
instance smulDistribClass_self (G A : Type*) [Monoid G] [Monoid A] [MulDistribMulAction G A] :
    SMulDistribClass G A A :=
  ⟨smul_mul'⟩

end TauCeti
