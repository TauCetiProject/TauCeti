/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
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
  `iteratedLoopSpaceHomeomorph_succ` its defining equations, and
  `iteratedLoopSpaceHomeomorph_map` its naturality in `X`.
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

/-- **Naturality of the currying homeomorphism**: `GenLoop.genLoopLoopHomeomorph` commutes with
the maps induced on cube loops by a based map `f` and by `Ω f`. -/
theorem genLoopLoopHomeomorph_map {X Y : BasedTopologicalSpace.{u}} (f : Hom X Y)
    (k : ℕ) (p : GenLoop (Fin k) X.loopSpace.carrier X.loopSpace.basepoint) :
    GenLoop.genLoopLoopHomeomorph Y.basepoint k
        (GenLoop.map f.loopSpace.toContinuousMap f.loopSpace.map_basepoint p) =
      GenLoop.map f.toContinuousMap f.map_basepoint
        (GenLoop.genLoopLoopHomeomorph X.basepoint k p) := by
  refine GenLoop.ext _ _ fun t => ?_
  rw [GenLoop.genLoopLoopHomeomorph_apply]
  exact (Hom.loopSpace_apply f _ _).trans
    (congrArg f (GenLoop.genLoopLoopHomeomorph_apply X.basepoint k p t).symm)

/-- **Naturality of the cube-loop homeomorphism**: a based map `f` acts on iterated loops
`Ω^[k] f` and on cube loops by postcomposition compatibly with `iteratedLoopSpaceHomeomorph`. -/
@[simp]
theorem iteratedLoopSpaceHomeomorph_map :
    (k : ℕ) → {X Y : BasedTopologicalSpace.{u}} → (f : Hom X Y) →
      (γ : (X.iteratedLoopSpace k).carrier) →
      iteratedLoopSpaceHomeomorph k Y (f.iteratedLoopSpace k γ) =
        GenLoop.map f.toContinuousMap f.map_basepoint (iteratedLoopSpaceHomeomorph k X γ)
  | 0, _, _, _, _ => by
    rw [Hom.iteratedLoopSpace_zero]
    exact GenLoop.ext _ _ fun _ => rfl
  | k + 1, _, _, f, γ => by
    rw [Hom.iteratedLoopSpace_succ]
    exact (congrArg (GenLoop.genLoopLoopHomeomorph _ k)
      (iteratedLoopSpaceHomeomorph_map k f.loopSpace γ)).trans
        (genLoopLoopHomeomorph_map f k _)

end BasedTopologicalSpace

end TauCeti
