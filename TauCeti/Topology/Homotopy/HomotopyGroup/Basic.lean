/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.Homotopy.Cube.Basic
import TauCeti.Topology.Homotopy.GenLoop.Homotopic

/-!
# Basic properties of homotopy groups

A pointed space is path connected if and only if its zeroth homotopy set is a subsingleton.
This follows from Mathlib's equivalence between the zeroth homotopy set and path components.

For an infinite index set the boundary of the cube is dense (`Cube.dense_boundary`). Hence a
generalized loop into a `T1` space is constant, so there is only one generalized loop
(`GenLoop.subsingleton_of_infinite`). In an arbitrary space every generalized loop is still
homotopic relative to the boundary to the constant loop (`GenLoop.homotopic_const_of_infinite`),
so the homotopy set is trivial (the instance `HomotopyGroup.subsingleton_of_infinite`).
-/

public section

open scoped Topology Topology.Homotopy
open HomotopyGroup Topology.Homotopy

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- A pointed space is path connected if and only if its zeroth homotopy set `π_ 0 X x` is a
subsingleton. -/
theorem pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (x : X) :
    PathConnectedSpace X ↔ Subsingleton (π_ 0 X x) := by
  rw [pathConnectedSpace_iff_zerothHomotopy]
  have hne : Nonempty (ZerothHomotopy X) := ⟨ZerothHomotopy.mk x⟩
  simp only [hne, true_and]
  exact (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x).symm.subsingleton_congr

end TauCeti

open scoped unitInterval in
/-- **There is at most one generalized loop indexed by an infinite set** in a `T1` space. -/
-- Such a loop is the base point on the dense boundary of the cube, and the fiber over the base
-- point is closed, so the loop is constant.
instance GenLoop.subsingleton_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    [T1Space X] {x : X} : Subsingleton (Ω^ N X x) :=
  have hconst (f : Ω^ N X x) (y : I^N) : f y = x :=
    closure_minimal (s := Cube.boundary N) (t := ⇑f ⁻¹' {x})
      (fun y hy ↦ GenLoop.boundary f y hy) (isClosed_singleton.preimage (map_continuous f))
      ((Cube.dense_boundary N) y)
  ⟨fun f g ↦ GenLoop.ext f g fun y ↦ (hconst f y).trans (hconst g y).symm⟩

open scoped unitInterval in
/-- **Generalized loops indexed by an infinite set are null-homotopic** in every space: each is
homotopic relative to the cube boundary to `GenLoop.const`. -/
theorem GenLoop.homotopic_const_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    {x : X} (f : Ω^ N X x) : GenLoop.Homotopic f GenLoop.const := by
  -- `f` is the base point `x` on the dense boundary of the cube, so each value `f y` lies in the
  -- closure of `{x}`, that is, `x` specializes to `f y`. Hence the constant loop specializes to
  -- `f` in the compact-open topology, so the two are joined by a path in `Ω^ N X x`, which is a
  -- homotopy relative to the boundary (`GenLoop.homotopic_iff_joined`).
  have hx (y : I^N) : x ⤳ f y := specializes_iff_mem_closure.2 <|
    map_mem_closure (map_continuous f) (Cube.dense_boundary N y) fun z hz ↦ GenLoop.boundary f z hz
  have h : (GenLoop.const : Ω^ N X x) ⤳ f :=
    (subtype_specializes_iff _ _).2 (ContinuousMap.specializes_coe.1 (specializes_pi.2 hx))
  exact GenLoop.homotopic_iff_joined.2
    (h.joinedIn (Set.mem_univ _) (Set.mem_univ _)).joined.symm

/-- **Homotopy sets indexed by an infinite set are trivial** in every space, since every
generalized loop is homotopic to the constant loop (`GenLoop.homotopic_const_of_infinite`). -/
instance HomotopyGroup.subsingleton_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    {x : X} : Subsingleton (HomotopyGroup N X x) :=
  ⟨Quotient.ind₂ fun f g ↦ Quotient.sound <|
    (GenLoop.homotopic_const_of_infinite f).trans (GenLoop.homotopic_const_of_infinite g).symm⟩
