/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.GenLoop.Homeomorph

/-!
# Homotopy of generalized loops is path connectedness

Mathlib defines `GenLoop.Homotopic`, homotopy of generalized loops relative to the cube
boundary, and separately topologises `Ω^ N X x` with the compact-open topology, but does not
relate the two. Two generalized loops are homotopic relative to the cube boundary exactly when
they are joined by a path in `Ω^ N X x`: currying a homotopy `I × I^N → X` gives the path, and
uncurrying a path gives the homotopy; the boundary condition is automatic in both directions,
because every generalized loop is constant at `x` on the cube boundary. Consequently any
homeomorphism between spaces of generalized loops preserves and reflects homotopy.

## Main declarations

* `GenLoop.homotopic_iff_joined`: homotopy relative to the cube boundary is path connectedness.
* `GenLoop.homotopic_homeomorph_iff`: a homeomorphism of generalized-loop spaces preserves and
  reflects homotopy.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {M N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
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

/-- A homeomorphism between spaces of generalized loops preserves and reflects homotopy
relative to the cube boundary: both are path connectedness, which a homeomorphism transports
in both directions. -/
@[simp]
theorem homotopic_homeomorph_iff (φ : Ω^ M X x ≃ₜ Ω^ N Y y) {p q : Ω^ M X x} :
    _root_.GenLoop.Homotopic (φ p) (φ q) ↔ _root_.GenLoop.Homotopic p q := by
  rw [homotopic_iff_joined, homotopic_iff_joined]
  refine ⟨fun h => ?_, fun h => h.map φ.continuous⟩
  simpa using h.map φ.symm.continuous

end GenLoop
