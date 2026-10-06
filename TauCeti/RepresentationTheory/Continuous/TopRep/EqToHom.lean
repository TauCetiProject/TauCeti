/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Transports between equal topological representations

This file supplements Mathlib's category `TopRep k G` of continuous representations with the
action of the transports `eqToHom h` along equalities `h : X = Y` of objects: on underlying
vectors they are casts of the carriers.

## Main results

* `TopRep.eqToHom_hom_apply`: a transport between equal objects casts the carrier.
-/

public section

namespace TopRep

open CategoryTheory

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Monoid G]

/-- For an equality `h : X = Y` of topological representations, the transport `eqToHom h` sends
`x : X` to its cast along the induced equality `X.V = Y.V` of carriers. -/
@[simp]
theorem eqToHom_hom_apply {X Y : TopRep k G} (h : X = Y) (x : X) :
    (eqToHom h).hom x = cast (congrArg TopRep.V h) x := by
  subst h
  rfl

end TopRep
