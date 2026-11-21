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
# Irreducible elements under multiplicative group actions

A group acting on a monoid by multiplicative automorphisms (`MulDistribMulAction`), such as a
`MulSemiringAction` on a ring, acts through multiplicative equivalences and therefore preserves and
reflects irreducibility.

## Main results

* `TauCeti.irreducible_smul_iff`: `Irreducible (g • a) ↔ Irreducible a`.
* `Irreducible.smul`: if `a` is irreducible, then so is `g • a`.
-/

public section

variable {G M : Type*} [Group G] [Monoid M] [MulDistribMulAction G M]

/-- A group acting on a monoid by multiplicative automorphisms preserves and reflects
irreducibility. -/
@[simp]
theorem TauCeti.irreducible_smul_iff (g : G) {a : M} :
    Irreducible (g • a) ↔ Irreducible a := by
  simpa only [MulDistribMulAction.toMulEquiv_apply] using
    MulEquiv.irreducible_iff (MulDistribMulAction.toMulEquiv M g) (x := a)

/-- A group acting on a monoid by multiplicative automorphisms preserves irreducible elements. -/
theorem Irreducible.smul {a : M} (ha : Irreducible a) (g : G) :
    Irreducible (g • a) :=
  (TauCeti.irreducible_smul_iff g).mpr ha
