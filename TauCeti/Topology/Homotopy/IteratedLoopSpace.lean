/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import TauCeti.Topology.Category.BasedTopologicalSpace

/-!
# Iterated loop spaces

The loop space of a based topological space, as Mathlib's `Path x x` based at the constant loop,
and its `k`-fold iterate. Iterated loop spaces are the based mapping spaces out of spheres,
`Map_*(S^k, X) ≅ Ω^[k] X`; the constructions here do not involve homotopy groups.

## Main declarations

* `TauCeti.BasedTopologicalSpace.loopSpace`: the loop space `Ω X`, based at the constant loop.
* `TauCeti.BasedTopologicalSpace.iteratedLoopSpace`: the `k`-fold iterated loop space `Ω^[k] X`,
  with `iteratedLoopSpace_zero` and `iteratedLoopSpace_succ` its two defining equations.
-/

public section

universe u

namespace TauCeti

namespace BasedTopologicalSpace

/-- The loop space `Ω X`: loops at the basepoint, based at the constant loop. -/
-- Exposed so that equivalences out of `iteratedLoopSpace` can be defined by recursion in other
-- modules; users should go through `iteratedLoopSpace_zero` and `iteratedLoopSpace_succ`.
@[expose] def loopSpace (X : BasedTopologicalSpace.{u}) : BasedTopologicalSpace.{u} where
  carrier := Path X.basepoint X.basepoint
  basepoint := Path.refl X.basepoint

/-- The `k`-fold iterated loop space `Ω^[k] X`, the `k`-th iterate of `loopSpace` at `X`. -/
-- Exposed for the same reason as `loopSpace`.
@[expose] def iteratedLoopSpace (X : BasedTopologicalSpace.{u}) (k : ℕ) :
    BasedTopologicalSpace.{u} :=
  loopSpace^[k] X

/-- The zeroth iterated loop space is the space itself. -/
@[simp]
theorem iteratedLoopSpace_zero (X : BasedTopologicalSpace.{u}) : X.iteratedLoopSpace 0 = X :=
  Function.iterate_zero_apply _ _

/-- The `(k + 1)`-fold iterated loop space is the loop space of the `k`-fold one. -/
@[simp]
theorem iteratedLoopSpace_succ (X : BasedTopologicalSpace.{u}) (k : ℕ) :
    X.iteratedLoopSpace (k + 1) = (X.iteratedLoopSpace k).loopSpace :=
  Function.iterate_succ_apply' _ _ _

@[simp]
theorem loopSpace_carrier (X : BasedTopologicalSpace.{u}) :
    X.loopSpace.carrier = Path X.basepoint X.basepoint :=
  rfl

@[simp]
theorem loopSpace_basepoint (X : BasedTopologicalSpace.{u}) :
    X.loopSpace.basepoint = Path.refl X.basepoint :=
  rfl

end BasedTopologicalSpace

end TauCeti
