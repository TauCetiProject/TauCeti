/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Homotopy of generalized loops

Mathlib defines `GenLoop.Homotopic`, homotopy of generalized loops relative to the cube
boundary, and separately topologises `Ω^ N X x` with the compact-open topology, but does not
relate the two. This file proves that they agree: two generalized loops are homotopic relative
to the cube boundary exactly when they are joined by a path in `Ω^ N X x`. Currying a homotopy
`I × I^N → X` gives the path, and uncurrying a path gives the homotopy; the boundary condition
is automatic in both directions, because every generalized loop is constant at `x` on the cube
boundary.

The file also treats homotopies in the base space: a homotopy between based maps must remain
fixed at the basepoint in order to induce a homotopy between their postcompositions with a
generalized loop. That construction is made explicit, and pointed-homotopic maps are shown to
induce the same map on every homotopy group, with the corresponding equality of bundled monoid
homomorphisms in positive dimensions.

This supplies the boundary-relative homotopy API and the pointed-homotopy part of the
higher-homotopy API requested in Stage 3, item 9 of the Tau Ceti universal-covers roadmap.

## Main declarations

* `GenLoop.homotopic_iff_joined`: **homotopy relative to the cube boundary is path
  connectedness in `Ω^ N X x`.**
* `HomotopyGroup.map_eq_of_homotopicRel`: pointed-homotopic maps induce the same map on
  homotopy groups.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-! ### Homotopy relative to the boundary is path connectedness -/

/-- The path in the space of generalized loops traced by a homotopy relative to the cube
boundary. Each stage of the homotopy is a generalized loop because the homotopy is stationary
on the cube boundary, where its initial stage takes the value `x`. -/
def pathOfHomotopyRel {p q : Ω^ N X x}
    (H : (p : C(I^N, X)).HomotopyRel q (Cube.boundary N)) : Path p q where
  toFun t := ⟨H.toContinuousMap.curry t, fun z hz =>
    (H.eq_fst t hz).trans (_root_.GenLoop.boundary p z hz)⟩
  continuous_toFun := (map_continuous H.toContinuousMap.curry).subtype_mk _
  source' := _root_.GenLoop.ext _ _ fun z => H.apply_zero z
  target' := _root_.GenLoop.ext _ _ fun z => H.apply_one z

@[simp]
theorem pathOfHomotopyRel_apply {p q : Ω^ N X x}
    (H : (p : C(I^N, X)).HomotopyRel q (Cube.boundary N)) (t : I) (z : I^N) :
    pathOfHomotopyRel H t z = H (t, z) :=
  by rw [pathOfHomotopyRel.eq_1]; rfl

/-- The homotopy relative to the cube boundary underlying a path in the space of generalized
loops. The relative condition is automatic: every stage of the path is a generalized loop, so
it takes the value `x` at every point of the cube boundary. -/
def homotopyRelOfPath {p q : Ω^ N X x} (γ : Path p q) :
    (p : C(I^N, X)).HomotopyRel q (Cube.boundary N) where
  toFun := (ContinuousMap.uncurry
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(Ω^ N X x, C(I^N, X))).comp γ.toContinuousMap))
  map_zero_left z := congrArg (fun r : Ω^ N X x => r z) γ.source
  map_one_left z := congrArg (fun r : Ω^ N X x => r z) γ.target
  prop' t z hz := ((γ t).property z hz).trans (_root_.GenLoop.boundary p z hz).symm

@[simp]
theorem homotopyRelOfPath_apply {p q : Ω^ N X x} (γ : Path p q) (t : I) (z : I^N) :
    homotopyRelOfPath γ (t, z) = γ t z :=
  by rw [homotopyRelOfPath.eq_1]; rfl

/-- **Two generalized loops are homotopic relative to the cube boundary exactly when they are
joined by a path in the space of generalized loops.** The compact-open topology on `Ω^ N X x`
therefore records the homotopy relation of `HomotopyGroup N X x` as its path components. -/
theorem homotopic_iff_joined {p q : Ω^ N X x} :
    _root_.GenLoop.Homotopic p q ↔ Joined p q :=
  ⟨fun h => ⟨pathOfHomotopyRel h.some⟩, fun h => ⟨homotopyRelOfPath h.some⟩⟩

/-! ### Homotopies in the base space -/

/-- Postcomposing a generalized loop with maps homotopic relative to a set containing the
basepoint gives homotopic generalized loops. The resulting homotopy is relative to the cube
boundary. -/
theorem map_homotopic_of_homotopicRel {f g : C(X, Y)} (hf : f x = y) {S : Set X}
    (hx : x ∈ S) (H : f.HomotopicRel g S) (p : Ω^ N X x) :
    _root_.GenLoop.Homotopic (map f hf p) (map g ((H.fst_eq_snd hx).symm.trans hf) p) := by
  obtain ⟨H⟩ := H
  refine ⟨⟨⟨⟨fun tp ↦ H (tp.1, p.1 tp.2), ?_⟩, ?_, ?_⟩, ?_⟩⟩
  · fun_prop
  · intro t
    simpa only [map, ContinuousMap.comp_apply, _root_.GenLoop.mk_apply] using H.apply_zero (p.1 t)
  · intro t
    simpa only [map, ContinuousMap.comp_apply, _root_.GenLoop.mk_apply] using H.apply_one (p.1 t)
  · intro t u hu
    exact H.eq_fst t (by rw [p.2 u hu]; exact hx)

end GenLoop

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Continuous maps homotopic relative to a set containing the basepoint induce the same
function on homotopy groups. -/
theorem map_eq_of_homotopicRel {f g : C(X, Y)} (hf : f x = y) {S : Set X}
    (hx : x ∈ S) (H : f.HomotopicRel g S) :
    map (N := N) f hf = map g ((H.fst_eq_snd hx).symm.trans hf) := by
  funext a
  refine Quotient.inductionOn a ?_
  intro p
  exact Quotient.sound (GenLoop.map_homotopic_of_homotopicRel hf hx H p)

/-- Continuous maps homotopic relative to a set containing the basepoint have equal induced
monoid homomorphisms on positive-dimensional homotopy groups. -/
theorem mapHom_eq_of_homotopicRel [DecidableEq N] [Nonempty N] {f g : C(X, Y)}
    (hf : f x = y) {S : Set X} (hx : x ∈ S) (H : f.HomotopicRel g S) :
    mapHom (N := N) f hf = mapHom g ((H.fst_eq_snd hx).symm.trans hf) :=
  MonoidHom.ext fun a ↦ congrFun (map_eq_of_homotopicRel hf hx H) a

end HomotopyGroup
