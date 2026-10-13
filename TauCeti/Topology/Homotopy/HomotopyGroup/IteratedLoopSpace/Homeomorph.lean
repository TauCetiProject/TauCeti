/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.IteratedLoopSpace

/-!
# Iterated loop spaces as spaces of cube loops

The `k`-fold iterated loop space `Ω^[k] X` of a based space, built from nested paths, is
homeomorphic to Mathlib's space `Ω^ (Fin k) X x` of continuous maps `I^k → X` sending the boundary
of the cube to the basepoint, by currying the cube directions one at a time. The homeomorphism
carries the basepoint (the constant iterated loop) to the constant cube loop.

## Main declarations

* `TauCeti.BasedTopologicalSpace.iteratedLoopSpaceHomeomorph`:
  `Ω^[k] X ≃ₜ Ω^ (Fin k) X x`, with `iteratedLoopSpaceHomeomorph_zero` and
  `iteratedLoopSpaceHomeomorph_succ` its defining equations.
-/

public section

universe u

open scoped Topology.Homotopy

namespace TauCeti

namespace BasedTopologicalSpace

-- The recursion typechecks by definitional unfolding of the exposed `iteratedLoopSpace`:
-- `Ω^[0] X` is `X`, and `Ω^[k + 1] X` is `Ω^[k] (Ω X)` (the iterate recurses on its argument),
-- whose carrier is `Path _ _` based at `Path.refl _`, the source of
-- `GenLoop.genLoopLoopHomeomorph`.
/-- The `k`-fold iterated loop space of a based space is homeomorphic to the space of
generalized loops `Ω^ (Fin k) X x`: maps `I^k → X` sending the boundary of the cube to the
basepoint. -/
noncomputable def iteratedLoopSpaceHomeomorph :
    (k : ℕ) → (X : BasedTopologicalSpace.{u}) →
      (X.iteratedLoopSpace k).carrier ≃ₜ GenLoop (Fin k) X.carrier X.basepoint
  | 0, X => (genLoopHomeoOfIsEmpty (Fin 0) X.basepoint).symm
  | k + 1, X =>
    (iteratedLoopSpaceHomeomorph k X.loopSpace).trans
      (GenLoop.genLoopLoopHomeomorph X.basepoint k)

/-- With no cube directions, the iterated loop space is the space itself. -/
@[simp]
theorem iteratedLoopSpaceHomeomorph_zero (X : BasedTopologicalSpace.{u}) :
    iteratedLoopSpaceHomeomorph 0 X = (genLoopHomeoOfIsEmpty (Fin 0) X.basepoint).symm := by
  rw [iteratedLoopSpaceHomeomorph.eq_1]

/-- The cube-loop homeomorphism for `k + 1` loops is the one for `k` loops of `Ω X`, followed by
currying the last cube direction. -/
@[simp]
theorem iteratedLoopSpaceHomeomorph_succ (X : BasedTopologicalSpace.{u}) (k : ℕ) :
    iteratedLoopSpaceHomeomorph (k + 1) X =
      (iteratedLoopSpaceHomeomorph k X.loopSpace).trans
        (GenLoop.genLoopLoopHomeomorph X.basepoint k) := by
  rw [iteratedLoopSpaceHomeomorph.eq_2]

-- Both cases are definitional for the same reason as in `iteratedLoopSpaceHomeomorph`.
/-- The homeomorphism is based: it carries the constant iterated loop to the constant cube
loop. -/
@[simp]
theorem iteratedLoopSpaceHomeomorph_basepoint :
    (k : ℕ) → (X : BasedTopologicalSpace.{u}) →
      iteratedLoopSpaceHomeomorph k X (X.iteratedLoopSpace k).basepoint =
        (GenLoop.const : GenLoop (Fin k) X.carrier X.basepoint)
  | 0, _ => GenLoop.ext _ _ fun _ => rfl
  | k + 1, X =>
    (congrArg (GenLoop.genLoopLoopHomeomorph X.basepoint k)
      (iteratedLoopSpaceHomeomorph_basepoint k X.loopSpace)).trans
        (GenLoop.genLoopLoopHomeomorph_const X.basepoint k)

end BasedTopologicalSpace

end TauCeti
