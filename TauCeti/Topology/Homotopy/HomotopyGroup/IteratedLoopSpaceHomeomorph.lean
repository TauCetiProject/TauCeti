/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.IteratedLoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Iterated loop spaces as spaces of cube loops

The `k`-fold iterated loop space `Ω^[k] X` of a based space, built from nested paths, is
homeomorphic to Mathlib's space `Ω^ (Fin k) X x` of continuous maps `I^k → X` sending the boundary
of the cube to the basepoint, by currying the cube directions one at a time. The homeomorphism
carries the basepoint (the constant iterated loop) to the constant cube loop.

## Main declarations

* `GenLoop.mapHomeomorph`: a based homeomorphism `X ≃ₜ Y` induces a homeomorphism of the
  generalized loop spaces `Ω^ N X x ≃ₜ Ω^ N Y y`.
* `GenLoop.loopGenLoopHomeomorph`: `Ω^ (Fin k) (Ω X x) ≃ₜ Ω^ (Fin (k + 1)) X x`.
* `TauCeti.BasedTopologicalSpace.iteratedLoopSpaceHomeomorph`:
  `Ω^[k] X ≃ₜ Ω^ (Fin k) X x`.
-/

public section

universe u

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- A homeomorphism `e : X ≃ₜ Y` with `e x = y` induces, by postcomposition, a homeomorphism of
the spaces of generalized loops `Ω^ N X x ≃ₜ Ω^ N Y y`. -/
def mapHomeomorph (e : X ≃ₜ Y) (h : e x = y) : Ω^ N X x ≃ₜ Ω^ N Y y where
  toFun := map ⟨e, e.continuous⟩ h
  invFun := map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm)
  left_inv p := _root_.GenLoop.ext _ _ fun t => e.symm_apply_apply (p t)
  right_inv p := _root_.GenLoop.ext _ _ fun t => e.apply_symm_apply (p t)
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp ⟨e, e.continuous⟩).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((ContinuousMap.continuous_postcomp ⟨e.symm, e.symm.continuous⟩).comp
      continuous_subtype_val).subtype_mk _

@[simp]
theorem mapHomeomorph_apply (e : X ≃ₜ Y) (h : e x = y) (p : Ω^ N X x) (t : I^N) :
    mapHomeomorph e h p t = e (p t) := by
  rw [mapHomeomorph.eq_1]; rfl

@[simp]
theorem mapHomeomorph_symm_apply (e : X ≃ₜ Y) (h : e x = y) (p : Ω^ N Y y) (t : I^N) :
    (mapHomeomorph e h).symm p t = e.symm (p t) := by
  rw [mapHomeomorph.eq_1]; rfl

variable (x) in
/-- Currying the last cube direction: cube loops in `k` directions of the loop space `Ω X x`,
based at the constant loop, are cube loops of `X` in `k + 1` directions. -/
def loopGenLoopHomeomorph (k : ℕ) :
    Ω^ (Fin k) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin (k + 1)) X x :=
  (mapHomeomorph (homeomorphOfUnique (Fin 1)).symm
      ((Homeomorph.symm_apply_eq _).mpr (homeomorphOfUnique_const (Fin 1)).symm)).trans
    ((genLoopGenLoopEquiv x).trans (GenLoop.congr x finSumFinEquiv))

variable (x) in
/-- The homeomorphism `loopGenLoopHomeomorph` is based: it carries the constant cube loop to
the constant cube loop. -/
@[simp]
theorem loopGenLoopHomeomorph_const (k : ℕ) :
    loopGenLoopHomeomorph x k (GenLoop.const : Ω^ (Fin k) (Ω X x) (Path.refl x)) =
      GenLoop.const := by
  rw [loopGenLoopHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  refine _root_.GenLoop.ext _ _ fun t => ?_
  simp

end GenLoop

namespace TauCeti

namespace BasedTopologicalSpace

/-- The `k`-fold iterated loop space of a based space is homeomorphic to the space of
generalized loops `Ω^ (Fin k) X x`: maps `I^k → X` sending the boundary of the cube to the
basepoint. -/
noncomputable def iteratedLoopSpaceHomeomorph :
    (k : ℕ) → (X : BasedTopologicalSpace.{u}) →
      (X.iteratedLoopSpace k).carrier ≃ₜ GenLoop (Fin k) X.carrier X.basepoint
  | 0, X => (genLoopHomeoOfIsEmpty (Fin 0) X.basepoint).symm
  | k + 1, X =>
    (iteratedLoopSpaceHomeomorph k X.loopSpace).trans
      (GenLoop.loopGenLoopHomeomorph X.basepoint k)

/-- The homeomorphism is based: it carries the constant iterated loop to the constant cube
loop. -/
theorem iteratedLoopSpaceHomeomorph_basepoint :
    (k : ℕ) → (X : BasedTopologicalSpace.{u}) →
      iteratedLoopSpaceHomeomorph k X (X.iteratedLoopSpace k).basepoint =
        (GenLoop.const : GenLoop (Fin k) X.carrier X.basepoint)
  | 0, _ => GenLoop.ext _ _ fun _ => rfl
  | k + 1, X =>
    (congrArg (GenLoop.loopGenLoopHomeomorph X.basepoint k)
      (iteratedLoopSpaceHomeomorph_basepoint k X.loopSpace)).trans
        (GenLoop.loopGenLoopHomeomorph_const X.basepoint k)

end BasedTopologicalSpace

end TauCeti
