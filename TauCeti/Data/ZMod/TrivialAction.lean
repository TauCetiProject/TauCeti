/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.ZMod.Defs

/-!
# The trivial action of a monoid on `ZMod n`

The trivial action `g • m = m` of a monoid `F` on `ZMod n`, as a `DistribMulAction`. Statements
about cohomology with trivial `ZMod n`-coefficients (for instance `H¹(G, 𝔽_p)` and `H²(G, 𝔽_p)`
of a profinite group `G`) need an action of `F` on `ZMod n` to form the coefficient module;
when no action of `F` appears in the conclusion, they install this one locally, either by
`let := trivialZModAction n F` or by `attribute [local instance] trivialZModAction`.

Since the action is trivial by definition, its triviality hypothesis `∀ g m, g • m = m` is
`fun _ _ ↦ rfl`, and for a topological monoid `F` the continuity of the action is
`⟨continuous_snd⟩`. For `n = 0` it is the trivial action on the integers.

## Main definitions

* `TauCeti.trivialZModAction`: the trivial action of a monoid on `ZMod n`.
-/

public section

namespace TauCeti

/-- The trivial action `g • m = m` of a monoid `F` on `ZMod n`: the coefficient action for
cohomology with trivial `ZMod n`-coefficients. -/
abbrev trivialZModAction (n : ℕ) (F : Type*) [Monoid F] : DistribMulAction F (ZMod n) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

end TauCeti
