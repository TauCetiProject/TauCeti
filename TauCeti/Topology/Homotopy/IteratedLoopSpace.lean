/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Iterated loop spaces

The loop space of a based topological space, as Mathlib's `Path x x` based at the constant loop,
and its `k`-fold iterate. These are the carriers of the mapping-space statements
`Map_*(S^k, X) ≅ Ω^[k] X` of the DG Floer development; they do not involve homotopy groups.

## Main declarations

* `TauCeti.BasedTopologicalSpace`: a topological space with a basepoint.
* `TauCeti.BasedTopologicalSpace.loopSpace`: the loop space `Ω X`, based at the constant loop.
* `TauCeti.BasedTopologicalSpace.iteratedLoopSpace`: the `k`-fold iterated loop space `Ω^[k] X`,
  with `iteratedLoopSpace_zero` and `iteratedLoopSpace_succ` its two defining equations.
-/

public section

universe u

namespace TauCeti

/-- A topological space with a basepoint. -/
structure BasedTopologicalSpace where
  /-- The underlying type. -/
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  /-- The basepoint. -/
  basepoint : carrier

attribute [instance] BasedTopologicalSpace.topologicalSpace

namespace BasedTopologicalSpace

/-- The loop space `Ω X`: loops at the basepoint, based at the constant loop. -/
@[expose] def loopSpace (X : BasedTopologicalSpace.{u}) : BasedTopologicalSpace.{u} where
  carrier := Path X.basepoint X.basepoint
  basepoint := Path.refl X.basepoint

/-- The `k`-fold iterated loop space `Ω^[k] X`, defined by `Ω^[0] X = X` and
`Ω^[k + 1] X = Ω (Ω^[k] X)`. -/
@[expose] def iteratedLoopSpace (X : BasedTopologicalSpace.{u}) : ℕ → BasedTopologicalSpace.{u}
  | 0 => X
  | k + 1 => (X.iteratedLoopSpace k).loopSpace

@[simp]
theorem iteratedLoopSpace_zero (X : BasedTopologicalSpace.{u}) : X.iteratedLoopSpace 0 = X := by
  rw [iteratedLoopSpace.eq_1]

@[simp]
theorem iteratedLoopSpace_succ (X : BasedTopologicalSpace.{u}) (k : ℕ) :
    X.iteratedLoopSpace (k + 1) = (X.iteratedLoopSpace k).loopSpace := by
  rw [iteratedLoopSpace.eq_2]

end BasedTopologicalSpace

end TauCeti
