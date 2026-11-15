/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.Homotopy.Homotopic.With

/-!
# Homotopy of generalized loops is path connectedness

Mathlib defines `GenLoop.Homotopic`, homotopy of generalized loops relative to the cube
boundary, and separately topologises `Ω^ N X x` with the compact-open topology, but does not
relate the two. Two generalized loops are homotopic relative to the cube boundary exactly when
they are joined by a path in `Ω^ N X x`. This is `ContinuousMap.homotopicWith_iff_joined` for the
predicate of being a generalized loop: since every generalized loop is constant at `x` on the cube
boundary, a homotopy fixes the boundary exactly when all of its stages are generalized loops.
Consequently any homeomorphism between spaces of generalized loops preserves and reflects
homotopy.

## Main declarations

* `GenLoop.homotopic_of_continuousMap`: a map `I × I^N → X` between two generalized loops that is
  stationary at the basepoint over the cube boundary is a homotopy relative to the boundary.
* `GenLoop.homotopic_iff_joined`: homotopy relative to the cube boundary is path connectedness.
* `Homeomorph.genLoopHomotopic_iff`: a homeomorphism of generalized-loop spaces preserves and
  reflects homotopy.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {M N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- A continuous map `I × I^N → X` from `p` to `q` that takes the value `x` over the cube boundary
is a homotopy of generalized loops relative to the cube boundary. -/
theorem homotopic_of_continuousMap {p q : Ω^ N X x} (H : C(I × I^N, X))
    (h₀ : ∀ z, H (0, z) = p z) (h₁ : ∀ z, H (1, z) = q z)
    (hb : ∀ t, ∀ z ∈ Cube.boundary N, H (t, z) = x) : _root_.GenLoop.Homotopic p q :=
  ⟨{ toContinuousMap := H
     map_zero_left := h₀
     map_one_left := h₁
     prop' t z hz := (hb t z hz).trans (_root_.GenLoop.boundary p z hz).symm }⟩

/-- **Two generalized loops are homotopic relative to the cube boundary exactly when they are
joined by a path in the space of generalized loops.** The compact-open topology on `Ω^ N X x`
therefore records the homotopy relation of `HomotopyGroup N X x` as its path components. -/
theorem homotopic_iff_joined {p q : Ω^ N X x} :
    _root_.GenLoop.Homotopic p q ↔ Joined p q := by
  -- Fixing the boundary values of `p` is the same as fixing them at `x`, i.e. as staying in
  -- `Ω^ N X x`, since `p` is itself a generalized loop.
  have hP : (fun h : C(I^N, X) => ∀ z ∈ Cube.boundary N, h z = (p : C(I^N, X)) z) =
      (· ∈ Ω^ N X x) :=
    funext fun h => propext <| forall₂_congr fun z hz => by
      rw [_root_.GenLoop.coe_coe, _root_.GenLoop.boundary p z hz]
  -- `GenLoop.Homotopic` unfolds to `HomotopicRel`, which is `HomotopicWith` for the predicate `hP`
  -- rewrites, and `Ω^ N X x` is the subtype `{h // h ∈ Ω^ N X x}`.
  change (p : C(I^N, X)).HomotopicWith q _ ↔ _
  rw [hP]
  exact ContinuousMap.homotopicWith_iff_joined p.2 q.2

/-- A homeomorphism between spaces of generalized loops preserves and reflects homotopy
relative to the cube boundary: both are path connectedness, which a homeomorphism transports
in both directions. -/
@[simp]
theorem _root_.Homeomorph.genLoopHomotopic_iff (φ : Ω^ M X x ≃ₜ Ω^ N Y y) {p q : Ω^ M X x} :
    _root_.GenLoop.Homotopic (φ p) (φ q) ↔ _root_.GenLoop.Homotopic p q := by
  rw [homotopic_iff_joined, homotopic_iff_joined]
  refine ⟨fun h => ?_, fun h => h.map φ.continuous⟩
  simpa using h.map φ.symm.continuous

end GenLoop
