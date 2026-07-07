/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Functoriality of homotopy groups

Mathlib defines the generalized loop space `Ω^ N X x` and the quotient
`HomotopyGroup N X x`, but it does not yet provide the map induced by a based continuous
map. This file supplies that small API: postcomposition sends generalized loops based at
`x` to generalized loops based at `y`, descends to homotopy classes, respects identity and
composition, and is a monoid homomorphism in positive dimensions.

This is a prerequisite for the higher-homotopy API requested in the Tau Ceti universal-covers
roadmap, Stage 3 item 9, before proving that a covering map induces isomorphisms on
`π_n` for `n ≥ 2`.
-/

public section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- A based continuous map sends generalized loops to generalized loops by postcomposition. -/
@[expose] def map (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) : Ω^ N Y y :=
  ⟨f.comp p.1, fun t ht => by simpa [hf] using congrArg f (_root_.GenLoop.boundary p t ht)⟩

@[simp]
theorem map_apply (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) (t : I^N) :
    map f hf p t = f (p t) :=
  rfl

@[simp]
theorem map_const (f : C(X, Y)) (hf : f x = y) :
    map f hf (_root_.GenLoop.const : Ω^ N X x) =
      (_root_.GenLoop.const : Ω^ N Y y) := by
  apply _root_.GenLoop.ext
  intro t
  simp [hf]

@[simp]
theorem map_id (p : Ω^ N X x) :
    map (ContinuousMap.id X) rfl p = p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

@[simp]
theorem map_comp (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (p : Ω^ N X x) :
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

namespace HomotopyGroup

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- The map on homotopy classes induced by a based continuous map. -/
@[expose] def map (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (GenLoop.map f hf) fun _ _ h => GenLoop.map_homotopic h f hf

@[simp]
theorem map_mk (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) :
    map f hf (⟦p⟧ : HomotopyGroup N X x) = ⟦GenLoop.map f hf p⟧ :=
  rfl

@[simp]
theorem map_id_apply (a : HomotopyGroup N X x) :
    map (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [map_mk, GenLoop.map_id]
    rfl

@[simp]
theorem map_comp_apply (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = map (g.comp f) (by simp [hf, hg]) a := by
  refine Quotient.inductionOn a ?_
  intro p
  simp

/-- In positive dimensions, the map induced by a based continuous map is a monoid
homomorphism for the standard group structure on homotopy groups. -/
@[expose] def mapHom [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    simp [_root_.HomotopyGroup.one_def]
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    simp [_root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N)]

@[simp]
theorem mapHom_apply [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    mapHom f hf a = map f hf a :=
  rfl

@[simp]
theorem map_mul [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y)
    (a b : HomotopyGroup N X x) :
    map f hf (a * b) = map f hf a * map f hf b :=
  (mapHom f hf).map_mul a b

@[simp]
theorem map_one [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y) :
    map f hf (1 : HomotopyGroup N X x) = 1 :=
  (mapHom f hf).map_one

end HomotopyGroup

end TauCeti
