/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Constant maps on homotopy groups

A constant based continuous map sends every generalized loop to the constant generalized
loop. Consequently, its induced function on homotopy classes is constant in every dimension,
and its induced monoid homomorphism is trivial in positive dimensions. Maps into a subsingleton
space specialize to this case.

These elimination rules extend the functoriality API requested in Stage 3, item 9 of the Tau
Ceti universal-covers roadmap. They are a prerequisite for using contractions to prove the
vanishing results in Stage 4.
-/

public section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

/-- Postcomposition by a constant continuous map gives the constant generalized loop. -/
@[simp]
theorem map_const_continuousMap (y : Y) (p : Ω^ N X x) :
    map (ContinuousMap.const X y) rfl p = (_root_.GenLoop.const : Ω^ N Y y) := by
  apply _root_.GenLoop.ext
  intro t
  rfl

end GenLoop

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- A constant continuous map sends every homotopy class to the class of the constant
generalized loop. This statement also covers dimension zero, where the target need not carry
the positive-dimensional group structure. -/
@[simp]
theorem map_const_apply (y : Y) (a : HomotopyGroup N X x) :
    map (x := x) (ContinuousMap.const X y) rfl a =
      (⟦(_root_.GenLoop.const : Ω^ N Y y)⟧ : HomotopyGroup N Y y) := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [map_mk, GenLoop.map_const_continuousMap]
  congr 1

/-- The function on homotopy groups induced by a constant map is constant. -/
theorem map_const (y : Y) :
    map (N := N) (x := x) (ContinuousMap.const X y) rfl =
      Function.const (HomotopyGroup N X x)
        (⟦(_root_.GenLoop.const : Ω^ N Y y)⟧ : HomotopyGroup N Y y) := by
  funext a
  exact map_const_apply y a

/-- A based map into a subsingleton space induces the same map as the constant map at the
target basepoint. -/
theorem map_eq_const_of_subsingleton [Subsingleton Y] (f : C(X, Y)) (hf : f x = y) :
    map (N := N) f hf = map (x := x) (ContinuousMap.const X y) rfl := by
  have h : f = ContinuousMap.const X y := Subsingleton.elim _ _
  subst f
  rfl

/-- In positive dimensions, a constant continuous map induces the trivial homomorphism on
homotopy groups. -/
@[simp]
theorem mapHom_const [DecidableEq N] [Nonempty N] (y : Y) :
    mapHom (N := N) (x := x) (ContinuousMap.const X y) rfl = 1 := by
  ext a
  rw [mapHom_apply, map_const_apply]
  exact _root_.HomotopyGroup.one_def.symm

/-- A based map into a subsingleton space induces the trivial homomorphism on every
positive-dimensional homotopy group. -/
theorem mapHom_eq_one_of_subsingleton [DecidableEq N] [Nonempty N] [Subsingleton Y]
    (f : C(X, Y)) (hf : f x = y) : mapHom (N := N) f hf = 1 := by
  have h : f = ContinuousMap.const X y := Subsingleton.elim _ _
  subst f
  exact mapHom_const (x := x) y

end HomotopyGroup

end TauCeti
