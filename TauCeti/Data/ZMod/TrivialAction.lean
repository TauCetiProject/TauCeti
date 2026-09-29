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

The trivial action `g • m = m` of a monoid `F` on `ZMod n`, as a `DistribMulAction`. It is the
coefficient action that a statement about the cohomology of trivial `ZMod n`-coefficients installs
locally when no action of `F` appears in its conclusion; the statements of
`TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationRank` that carry an action of `F` on
`ZMod n` as an instance together with the hypothesis that it is trivial then apply to it.

## Main definitions

* `TauCeti.trivialZModAction`: the trivial action of a monoid on `ZMod n`.
-/

public section

namespace TauCeti

-- The action is trivial by definition, so its triviality hypothesis is `fun _ _ ↦ rfl` and, for a
-- topological monoid `F`, the continuity of the action is `⟨continuous_snd⟩`; a statement whose
-- conclusion mentions no action of `F` installs it locally by `let := trivialZModAction n F`.
/-- The trivial action `g • m = m` of a monoid `F` on `ZMod n`. It is the coefficient action of a
statement about the cohomology of trivial `ZMod n`-coefficients whose conclusion mentions no action
of `F`. -/
abbrev trivialZModAction (n : ℕ) (F : Type*) [Monoid F] : DistribMulAction F (ZMod n) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

end TauCeti
