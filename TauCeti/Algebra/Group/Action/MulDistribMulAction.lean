/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# A multiplicative action on a monoid is distributive over its self-action

A multiplicative distributive action of `G` on a monoid `A`, such as a `MulSemiringAction`, has
`g • (a * b) = g • a * g • b`. Read with `A` acting on itself by left multiplication, this is
`SMulDistribClass G A A`, the form taken by statements about semilinear actions on `A`-modules
when the module is `A` itself. When `G` is a group, each `g • ·` is a multiplicative
automorphism of `A`, so it preserves irreducibility.

## Main results

* `TauCeti.smulDistribClass_self`: `SMulDistribClass G A A` for a `MulDistribMulAction G A`.
* `TauCeti.irreducible_smul_iff` and `Irreducible.smul`: irreducibility is preserved by a
  multiplicative distributive group action.
-/

public section

namespace TauCeti

/-- A multiplicative distributive action of `G` on a monoid `A` distributes over the action of `A`
on itself by left multiplication. -/
instance smulDistribClass_self (G A : Type*) [Monoid G] [Monoid A] [MulDistribMulAction G A] :
    SMulDistribClass G A A :=
  ⟨smul_mul'⟩

/-- A group acting by multiplicative distributive automorphisms preserves irreducibility. -/
theorem irreducible_smul_iff {G A : Type*} [Group G] [Monoid A] [MulDistribMulAction G A]
    (g : G) (a : A) : Irreducible (g • a) ↔ Irreducible a :=
  MulEquiv.irreducible_iff (MulDistribMulAction.toMulEquiv A g)

end TauCeti

/-- Irreducibility is preserved by a multiplicative distributive group action. -/
theorem Irreducible.smul {G A : Type*} [Group G] [Monoid A] [MulDistribMulAction G A]
    {a : A} (ha : Irreducible a) (g : G) : Irreducible (g • a) :=
  (TauCeti.irreducible_smul_iff g a).mpr ha
