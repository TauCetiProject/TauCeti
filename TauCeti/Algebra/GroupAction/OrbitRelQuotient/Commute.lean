/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Commuting actions on orbit spaces

Let a group `K` act on `Z`, and let `L` act on `Z` by maps commuting with the action of `K`
(`SMulCommClass L K Z`). Then each `l : L` carries `K`-orbits to `K`-orbits, so `L` acts on the
orbit space `Z ⧸ K = MulAction.orbitRel.Quotient K Z` by `l • [z] = [l • z]`
(`MulAction.orbitRel.Quotient.smul_mk`), and this is a monoid action when the action on `Z` is
(`MulAction.orbitRel.Quotient.instMulActionOfSMulCommClass`).

Such actions are the residual symmetries of quotient constructions: a group commuting with the
action of `K` on a manifold acts on the orbit manifold, and a symmetry of a Hamiltonian system
commuting with a symmetry group acts on the symplectic reduction.

## Main declarations

* `MulAction.orbitRel.Quotient.instSMulOfSMulCommClass`,
  `MulAction.orbitRel.Quotient.instMulActionOfSMulCommClass`: the action on the orbit space, and
  their additive versions.
* `MulAction.orbitRel.Quotient.smul_mk`: the action is computed on representatives.
-/

public section

namespace MulAction.orbitRel.Quotient

variable {L K Z : Type*} [Group K] [MulAction K Z]

/-- An action on `Z` commuting with the action of `K` acts on the space of `K`-orbits, by
translating representatives. -/
@[to_additive /-- An additive action on `Z` commuting with the additive action of `K` acts on the
space of `K`-orbits, by translating representatives. -/]
instance instSMulOfSMulCommClass [SMul L Z] [SMulCommClass L K Z] :
    SMul L (orbitRel.Quotient K Z) where
  smul l := Quotient.map (l • ·) fun _ z' hz ↦ by
    obtain ⟨k, rfl⟩ := MulAction.orbitRel_apply.1 hz
    exact MulAction.orbitRel_apply.2 ⟨k, (smul_comm l k z').symm⟩

/-- The action of a commuting action on `K`-orbits is computed on representatives. -/
@[to_additive (attr := simp) /-- The action of a commuting additive action on `K`-orbits is
computed on representatives. -/]
theorem smul_mk [SMul L Z] [SMulCommClass L K Z] (l : L) (z : Z) :
    l • Quotient.mk (orbitRel K Z) z = Quotient.mk (orbitRel K Z) (l • z) :=
  rfl

/-- A monoid action on `Z` commuting with the action of `K` descends to a monoid action on the
space of `K`-orbits. -/
@[to_additive /-- An additive monoid action on `Z` commuting with the additive action of `K`
descends to an additive monoid action on the space of `K`-orbits. -/]
instance instMulActionOfSMulCommClass [Monoid L] [MulAction L Z] [SMulCommClass L K Z] :
    MulAction L (orbitRel.Quotient K Z) where
  one_smul q := by
    induction q using Quotient.inductionOn with
    | h z => rw [smul_mk, one_smul]
  mul_smul l l' q := by
    induction q using Quotient.inductionOn with
    | h z => rw [smul_mk, smul_mk, smul_mk, mul_smul]

end MulAction.orbitRel.Quotient
