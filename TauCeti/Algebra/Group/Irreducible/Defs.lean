/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Basic.Nontrivial.Defs

/-!
# Irreducible elements and nontriviality

A monoid with an irreducible element is nontrivial, since `1` is not irreducible.
-/

public section

namespace Irreducible

/-- A monoid with an irreducible element is nontrivial, since `1` is not irreducible. -/
@[to_additive /-- An additive monoid with an additively irreducible element is nontrivial, since
`0` is not additively irreducible. -/]
theorem nontrivial {M : Type*} [Monoid M] {p : M} (hp : Irreducible p) : Nontrivial M :=
  nontrivial_of_ne p 1 hp.ne_one

end Irreducible
