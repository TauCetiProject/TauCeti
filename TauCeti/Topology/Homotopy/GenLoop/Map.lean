/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Functoriality of generalized loops

Mathlib defines the generalized loop space `Ω^ N X x`, the maps `I^N → X` sending the cube boundary
to `x`. This file supplies the map induced by a based continuous map: postcomposition sends
generalized loops based at `x` to generalized loops based at `y`; it respects identity and
composition, constant maps, homotopies relative to the cube boundary, and concatenation and
inversion in a cube direction.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- A based continuous map sends generalized loops to generalized loops by postcomposition. -/
def map (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) : Ω^ N Y y :=
  ⟨f.comp p.1, fun t ht => by simpa [hf] using congrArg f (_root_.GenLoop.boundary p t ht)⟩

@[simp]
theorem map_apply (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) (t : I^N) :
    map f hf p t = f (p t) := by
  rw [map]; rfl

/-- The underlying continuous map of `GenLoop.map f hf p` is the composite `f ∘ p`. -/
theorem coe_map (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) :
    ((map f hf p : Ω^ N Y y) : C(I^N, Y)) = f.comp (p : C(I^N, X)) := by
  rw [map]

/-- Postcomposition `GenLoop.map f` is continuous for the compact-open topologies on spaces of
generalized loops. -/
theorem continuous_map (f : C(X, Y)) (hf : f x = y) :
    Continuous (map (N := N) f hf) := by
  refine Continuous.subtype_mk ?_ _
  exact (ContinuousMap.continuous_postcomp f).comp continuous_subtype_val

@[simp]
theorem map_const (f : C(X, Y)) (hf : f x = y) :
    map f hf (_root_.GenLoop.const : Ω^ N X x) =
      (_root_.GenLoop.const : Ω^ N Y y) := by
  apply _root_.GenLoop.ext
  intro t
  simp [hf]

/-- Postcomposition by a constant continuous map gives the constant generalized loop.

This is not a `simp` lemma: baking the basepoint proof `rfl` into the statement forces the
target basepoint to be `(ContinuousMap.const X y) x` rather than `y`, so `simp` cannot close
even its own statement. Use it as an explicit rewrite. -/
theorem map_continuousMap_const (y : Y) (p : Ω^ N X x) :
    map (ContinuousMap.const X y) rfl p = (_root_.GenLoop.const : Ω^ N Y y) := by
  apply _root_.GenLoop.ext
  intro t
  rw [map_apply]
  exact _root_.GenLoop.const_apply.symm

@[simp]
theorem map_id (p : Ω^ N X x) :
    map (ContinuousMap.id X) rfl p = p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

@[simp]
theorem map_comp (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) :
    map g hg (map f hf p) = map (g.comp f) (by simp [hf, hg]) p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

/-- Postcomposition preserves homotopy relative to the cube boundary. -/
theorem map_homotopic {f g : Ω^ N X x} (h : _root_.GenLoop.Homotopic f g)
    (F : C(X, Y)) (hF : F x = y) :
    _root_.GenLoop.Homotopic (map F hF f) (map F hF g) :=
  ContinuousMap.HomotopicRel.comp_continuousMap h F

variable [DecidableEq N]

@[simp]
theorem map_transAt (F : C(X, Y)) (hF : F x = y) (i : N) (p q : Ω^ N X x) :
    map F hF (_root_.GenLoop.transAt i p q) =
      _root_.GenLoop.transAt i (map F hF p) (map F hF q) := by
  apply _root_.GenLoop.ext
  intro t
  simp only [map_apply, _root_.GenLoop.transAt, _root_.GenLoop.coe_copy]
  split_ifs <;> rfl

@[simp]
theorem map_symmAt (F : C(X, Y)) (hF : F x = y) (i : N) (p : Ω^ N X x) :
    map F hF (_root_.GenLoop.symmAt i p) =
      _root_.GenLoop.symmAt i (map F hF p) := by
  apply _root_.GenLoop.ext
  intro t
  simp only [map_apply, _root_.GenLoop.symmAt, _root_.GenLoop.coe_copy]

end GenLoop
