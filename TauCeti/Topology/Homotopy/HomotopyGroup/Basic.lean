/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.Homotopy.Cube.Basic

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
/-- **Generalized loops indexed by an infinite set are constant** in a `T1` space: such a loop is
the base point on the dense boundary of the cube, and the fiber over the base point is closed. -/
instance GenLoop.subsingleton_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    [T1Space X] {x : X} : Subsingleton (Ω^ N X x) :=
  have hconst (f : Ω^ N X x) (y : I^N) : f y = x :=
    closure_minimal (s := Cube.boundary N) (t := ⇑f ⁻¹' {x})
      (fun y hy ↦ GenLoop.boundary f y hy) (isClosed_singleton.preimage (map_continuous f))
      ((Cube.dense_boundary N) y)
  ⟨fun f g ↦ GenLoop.ext f g fun y ↦ (hconst f y).trans (hconst g y).symm⟩

open scoped unitInterval in
/-- **Generalized loops indexed by an infinite set are null-homotopic** in every space. Such a
loop `f` is the base point `x` on the dense boundary of the cube, so each value `f y` lies in the
closure of `{x}`: every open set containing `f y` contains `x`. Hence the map that is `f` at time
`0` and the base point at every later time is continuous, and it is a homotopy relative to the
boundary from `f` to the constant loop. -/
theorem GenLoop.homotopic_const_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    {x : X} (f : Ω^ N X x) : GenLoop.Homotopic f GenLoop.const := by
  have hx (y : I^N) : x ⤳ f y := specializes_iff_mem_closure.2 <|
    map_mem_closure (map_continuous f) (Cube.dense_boundary N y) fun z hz ↦ GenLoop.boundary f z hz
  have hcont : Continuous fun p : I × I^N ↦ if p.1 = 0 then f p.2 else x := by
    refine continuous_iff_continuousAt.2 fun ⟨t, y⟩ ↦ ?_
    by_cases ht : t = 0
    · subst ht
      refine tendsto_nhds.2 fun V hV hfy ↦ ?_
      replace hfy : f y ∈ V := by simpa using hfy
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        ((hV.preimage (map_continuous f)).mem_nhds hfy)] with p (hp : f p.2 ∈ V)
      change (if p.1 = 0 then f p.2 else x) ∈ V
      split_ifs
      exacts [hp, (hx y).mem_open hV hfy]
    · refine (continuousAt_const (y := x)).congr ?_
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds ht)]
        with p hp
      exact (ite_eq_right hp).symm
  exact ⟨{ toFun := fun p ↦ if p.1 = 0 then f p.2 else x
           continuous_toFun := hcont
           map_zero_left := fun _ ↦ ite_eq_left rfl
           map_one_left := fun _ ↦ ite_eq_right one_ne_zero
           prop' := fun t y hy ↦ by
             change (if t = 0 then f y else x) = f y
             split_ifs
             exacts [rfl, (GenLoop.boundary f y hy).symm] }⟩

/-- **Homotopy sets indexed by an infinite set are trivial** in every space, since every
generalized loop is homotopic to the constant loop (`GenLoop.homotopic_const_of_infinite`). -/
instance HomotopyGroup.subsingleton_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    {x : X} : Subsingleton (HomotopyGroup N X x) :=
  ⟨Quotient.ind₂ fun f g ↦ Quotient.sound <|
    (GenLoop.homotopic_const_of_infinite f).trans (GenLoop.homotopic_const_of_infinite g).symm⟩
