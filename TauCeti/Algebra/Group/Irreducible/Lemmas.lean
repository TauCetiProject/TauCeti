/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# Irreducible elements under multiplicative distributive group actions

Every element of a group acting on a monoid by multiplicative automorphisms (`MulDistribMulAction`)
defines a multiplicative equivalence, and therefore preserves and reflects irreducibility.

## Main results

* `TauCeti.irreducible_smul_iff`: for a `MulDistribMulAction` of a group `G` on a monoid `M`,
  `g • x` is irreducible if and only if `x` is irreducible.
* `Irreducible.smul`: acting by a group element preserves irreducibility.
-/

public section

namespace TauCeti

/-- Acting by a group element via a multiplicative distributive action preserves and reflects
irreducibility. -/
@[simp]
theorem irreducible_smul_iff {G M : Type*} [Group G] [Monoid M] [MulDistribMulAction G M]
    (g : G) {x : M} : Irreducible (g • x) ↔ Irreducible x :=
  MulEquiv.irreducible_iff (MulDistribMulAction.toMulEquiv M g)

end TauCeti

namespace Irreducible

/-- Acting by a group element via a multiplicative distributive action preserves irreducibility. -/
theorem smul {G M : Type*} [Group G] [Monoid M] [MulDistribMulAction G M]
    {x : M} (hx : Irreducible x) (g : G) : Irreducible (g • x) :=
  (TauCeti.irreducible_smul_iff g).mpr hx

end Irreducible
