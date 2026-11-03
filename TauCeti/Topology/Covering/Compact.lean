/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Basic
import TauCeti.Topology.Covering.Clopen
import TauCeti.Topology.Homotopy.Covering

/-!
# Local homeomorphisms out of compact spaces

A local homeomorphism `f : M → N` from a compact path-connected Hausdorff space to a simply
connected Hausdorff space is bijective. By Mathlib's
`isLocalHomeomorph_iff_isCoveringMap`, a local homeomorphism from a compact Hausdorff space to a
Hausdorff space is a covering map. A covering map from a nonempty space onto a connected space is
surjective (`IsCoveringMap.surjective`), and a covering map from a path-connected space onto a
simply connected space is injective (`IsCoveringMap.injective`).

## Main declarations

* `IsLocalHomeomorph.bijective_of_compactSpace`: a local homeomorphism from a compact
  path-connected Hausdorff space to a simply connected Hausdorff space is bijective.
-/

public section

open Function

namespace TauCeti

/-- **A local homeomorphism from a compact path-connected space to a simply connected space is
bijective.** Both spaces are Hausdorff. -/
theorem _root_.IsLocalHomeomorph.bijective_of_compactSpace {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [CompactSpace M] [PathConnectedSpace M] [T2Space M] [T2Space N]
    [SimplyConnectedSpace N] {f : M → N} (hf : IsLocalHomeomorph f) : Bijective f := by
  have hcov : IsCoveringMap f := isLocalHomeomorph_iff_isCoveringMap.mp hf
  exact ⟨hcov.injective, hcov.surjective⟩

end TauCeti
