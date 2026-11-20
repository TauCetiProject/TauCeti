/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.GenLoop.Loop
public import TauCeti.Topology.Homotopy.IteratedLoopSpace.Basic

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
  `iteratedLoopSpaceHomeomorph_map` its naturality in `X`,
  `iteratedLoopSpaceHomeomorph_zero_apply` and `iteratedLoopSpaceHomeomorph_succ_apply` its
  values, and `iteratedLoopSpaceHomeomorph_one_apply` and `iteratedLoopSpaceHomeomorph_two_apply`
  its values on loops and double loops.
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

/-- The inverse of the homeomorphism carries the constant cube loop to the constant iterated
loop. -/
@[simp]
theorem iteratedLoopSpaceHomeomorph_symm_const (k : ℕ) (X : BasedTopologicalSpace.{u}) :
    (iteratedLoopSpaceHomeomorph k X).symm
        (GenLoop.const : GenLoop (Fin k) X.carrier X.basepoint) =
      (X.iteratedLoopSpace k).basepoint :=
  (iteratedLoopSpaceHomeomorph k X).symm_apply_eq.2
    (iteratedLoopSpaceHomeomorph_basepoint k X).symm

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
    exact GenLoop.ext _ _ fun _ => by rw [GenLoop.map_apply]; rfl
  | k + 1, _, _, f, γ => by
    rw [Hom.iteratedLoopSpace_succ]
    exact (congrArg (GenLoop.genLoopLoopHomeomorph _ k)
      (iteratedLoopSpaceHomeomorph_map k f.loopSpace γ)).trans
        (ContinuousMap.genLoopLoopHomeomorph_map f.toContinuousMap f.map_basepoint
          f.loopSpace.toContinuousMap (fun γ t => Hom.loopSpace_apply' f γ t) k _)

-- `Ω^[0] X` is `X` by definitional unfolding of the exposed `iteratedLoopSpace`, so a point of
-- `X` is an element of its carrier.
/-- With no cube directions, the cube loop of a point `x` is constant at `x`: the inverse of
Mathlib's `genLoopHomeoOfIsEmpty` sends a point to the constant generalized loop at it. -/
theorem iteratedLoopSpaceHomeomorph_zero_apply (X : BasedTopologicalSpace.{u}) (x : X.carrier)
    (t : Fin 0 → unitInterval) :
    iteratedLoopSpaceHomeomorph 0 X x t = x := by
  rw [iteratedLoopSpaceHomeomorph_zero]
  -- The inverse of `genLoopHomeoOfIsEmpty` is the constant generalized loop.
  rfl

-- `Ω^[k + 1] X` is `Ω^[k] (Ω X)` by definitional unfolding of the exposed `iteratedLoopSpace`, so
-- the cube loop of `γ` in `k` directions of `Ω X` takes values in loops of `X`.
/-- The cube loop of an iterated loop `γ` in `k + 1` directions is computed from its cube loop in
`k` directions of `Ω X`: the last cube direction is the loop parameter. -/
theorem iteratedLoopSpaceHomeomorph_succ_apply (X : BasedTopologicalSpace.{u}) (k : ℕ)
    (γ : (X.iteratedLoopSpace (k + 1)).carrier) (t : Fin (k + 1) → unitInterval) :
    iteratedLoopSpaceHomeomorph (k + 1) X γ t =
      (iteratedLoopSpaceHomeomorph k X.loopSpace γ (fun i => t i.castSucc) :
        Path X.basepoint X.basepoint) (t (Fin.last k)) := by
  rw [iteratedLoopSpaceHomeomorph_succ]
  -- `Homeomorph.trans_apply` holds by `rfl`; it cannot be rewritten with here because
  -- `Ω^ (Fin k) X.loopSpace.carrier _` is the source of `genLoopLoopHomeomorph` only up to
  -- unfolding `BasedTopologicalSpace.loopSpace`.
  exact GenLoop.genLoopLoopHomeomorph_apply X.basepoint k
    (iteratedLoopSpaceHomeomorph k X.loopSpace γ) t

-- `Ω^[1] X` is `Ω X` by definitional unfolding of the exposed `iteratedLoopSpace`, so a loop is
-- an element of its carrier.
/-- A loop `γ`, read as a cube loop in one direction, takes the value `γ t₀` at `t₀`. -/
theorem iteratedLoopSpaceHomeomorph_one_apply (X : BasedTopologicalSpace.{u})
    (γ : Path X.basepoint X.basepoint) (t : Fin 1 → unitInterval) :
    iteratedLoopSpaceHomeomorph 1 X γ t = γ (t 0) :=
  -- `γ` lies in `(X.iteratedLoopSpace 1).carrier` only up to unfolding, so `rw` cannot match the
  -- successor step; it is chained with `Eq.trans` instead.
  (iteratedLoopSpaceHomeomorph_succ_apply X 0 γ t).trans
    (congrArg (fun γ' : Path X.basepoint X.basepoint => γ' (t (Fin.last 0)))
      (iteratedLoopSpaceHomeomorph_zero_apply X.loopSpace γ _))

-- `Ω^[2] X` is `Ω (Ω X)` by definitional unfolding of the exposed `iteratedLoopSpace`, so a double
-- loop is an element of its carrier.
/-- A double loop `γ`, read as a cube loop in two directions, takes the value `γ t₀ t₁` at
`(t₀, t₁)`: the first coordinate is the loop parameter of the loop of loops. -/
theorem iteratedLoopSpaceHomeomorph_two_apply (X : BasedTopologicalSpace.{u})
    (γ : Path (Path.refl X.basepoint) (Path.refl X.basepoint)) (t : Fin 2 → unitInterval) :
    iteratedLoopSpaceHomeomorph 2 X γ t = γ (t 0) (t 1) :=
  -- As in `iteratedLoopSpaceHomeomorph_one_apply`, the successor step is chained with `Eq.trans`.
  (iteratedLoopSpaceHomeomorph_succ_apply X 1 γ t).trans
    (congrArg (fun γ' : Path X.basepoint X.basepoint => γ' (t (Fin.last 1)))
      (iteratedLoopSpaceHomeomorph_one_apply X.loopSpace γ _))

end BasedTopologicalSpace

end TauCeti
