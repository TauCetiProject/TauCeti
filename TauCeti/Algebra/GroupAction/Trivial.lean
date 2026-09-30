/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Trivial actions

A trivial action of `G` on `R`, `g • m = m` for all `g` and `m`, given as a hypothesis rather than
as an instance: this is how the trivial coefficient modules of group cohomology are handled, where
the action of `G` on a ring of coefficients is a parameter and its triviality a hypothesis
(`TauCeti.cohomFpAddEquivH1`).

When a construction demands an action as an instance and the ambient theory has none, the trivial
action of a monoid `G` on a monoid `M` by monoid endomorphisms is supplied by
`TauCeti.trivialMulDistribMulAction`, deliberately not an instance: it is installed locally where it
is needed, as in the theory of projective representations and for central extensions such as
`1 → ℤ/2 → ℤ/4 → ℤ/2 → 1`.

## Main results

* `TauCeti.smul_mul_smul_of_smul_eq_self`: for a trivial action on a multiplicative structure,
  multiplication is equivariant, `g • m * g • n = g • (m * n)`.
* `TauCeti.bot_smul_eq_bot_smul`: actions by two trivial subgroups agree.
* `TauCeti.trivialMulDistribMulAction`: the trivial action of a monoid on a monoid by monoid
  endomorphisms, with `TauCeti.trivialMulDistribMulAction_smul`: under it every element is fixed.
-/

public section

namespace TauCeti

section BottomSubgroup

variable {G : Type*} [Group G] {U : Subgroup G} {A : Type*}

/-- Two actions of trivial subgroups on the same type agree: a trivial group acts trivially. -/
theorem bot_smul_eq_bot_smul [MulAction (⊥ : Subgroup U) A] [MulAction (⊥ : Subgroup G) A]
    (v : (⊥ : Subgroup U)) (w : (⊥ : Subgroup G)) (a : A) : w • a = v • a := by
  rw [Subsingleton.elim v 1, Subsingleton.elim w 1, one_smul, one_smul]

end BottomSubgroup

variable {G : Type*} {R : Type*} [Mul R] [SMul G R]

/-- For a trivial action of `G` on a multiplicative structure, multiplication is equivariant. -/
theorem smul_mul_smul_of_smul_eq_self (htriv : ∀ (g : G) (m : R), g • m = m) (g : G) (m n : R) :
    g • m * g • n = g • (m * n) := by
  rw [htriv, htriv, htriv]

/-- **The trivial action of a monoid `G` on a monoid `M`**, `g • a = a`, obtained by composing the
tautological action of `MulAut M` with the trivial homomorphism. It is the action for which the
extension built from a factor set is central, so it is the one a projective representation's factor
set is bundled over in `TauCeti.IsProjectiveRep.exists_factorSet_linearization`. It is reducible and
deliberately not an instance, since the theory of factor sets is stated for an arbitrary action; it
is only used to supply one where the ambient theory has none. -/
abbrev trivialMulDistribMulAction (G M : Type*) [Monoid G] [Monoid M] :
    MulDistribMulAction G M :=
  MulDistribMulAction.compHom M (1 : G →* MulAut M)

section TrivialActionSmul

attribute [local instance] trivialMulDistribMulAction

/-- Under `TauCeti.trivialMulDistribMulAction` every element is fixed. This is the triviality
hypothesis that `TauCeti.FactorSet.isFactorSet_curry`, `TauCeti.IsFactorSet.toFactorSet` and
`TauCeti.FactorSet.inl_range_le_center` take, supplied once so that their callers can name a
constant rather than an inlined proof. -/
@[simp]
theorem trivialMulDistribMulAction_smul {G M : Type*} [Monoid G] [Monoid M] (g : G) (a : M) :
    g • a = a :=
  rfl

end TrivialActionSmul

end TauCeti
