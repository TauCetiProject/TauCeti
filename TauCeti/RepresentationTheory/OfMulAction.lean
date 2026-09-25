/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Commuting permutation representations

If monoids `G` and `H` act on a type `X` and the two actions commute, then the permutation
representations `Representation.ofMulAction k G X` and `Representation.ofMulAction k H X` on the
free `k`-module `k[X]` commute with each other. For the left and right multiplication actions of
a group `G`, that is, commuting actions of `G` and `Gᵐᵒᵖ`, this makes `k[X]` a `k[G]`-bimodule.

## Main results

* `TauCeti.commute_ofMulAction`: commuting actions on `X` give commuting permutation
  representations on `k[X]`.
-/

public section

namespace TauCeti

open Representation

variable {k G H X : Type*} [Semiring k] [Monoid G] [Monoid H] [MulAction G X] [MulAction H X]

/-- If the actions of `G` and `H` on `X` commute, then so do the permutation representations of
`G` and `H` on `k[X]`. -/
theorem commute_ofMulAction [SMulCommClass G H X] (g : G) (h : H) :
    Commute (ofMulAction k G X g) (ofMulAction k H X h) := by
  ext
  simp [smul_comm g h]

end TauCeti
