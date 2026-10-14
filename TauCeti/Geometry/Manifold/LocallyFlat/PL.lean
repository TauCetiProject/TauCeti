/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Topology.PL.Map

/-!
# Piecewise-linear graphs are locally flat

The graph of a continuous map is locally flat, by the continuous-graph theorem in
`TauCeti.Geometry.Manifold.LocallyFlat.Basic`. This file combines that result with the
piecewise-linear continuity theorem for consumers building PL embeddings.

This is the graph building block for the locally flat embedding side of geometric topology. The
non-affine statement applies, for example, to the absolute-value PL map. The graph-chart
criterion below transports this local model through an ambient homeomorphism.
-/

public section

namespace TauCeti

/-- A map piecewise linear on all of `E` has a locally flat graph `x ↦ (x, f x)` with
complementary model `F`. -/
theorem IsPLOn.isLocallyFlat_graph
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] {f : E → F}
    (hf : IsPLOn f (Set.univ : Set E)) :
    IsLocallyFlat E F (fun x : E => (x, f x)) :=
  TauCeti.isLocallyFlat_graph f (continuousOn_univ.mp hf.continuousOn)

/-- A globally PL map is locally flat when an ambient homeomorphism presents its image as a graph.
The section equation `(Φ (f x)).1 = x` identifies `f` with that graph, with complementary model
`F`. -/
theorem IsPLOn.isLocallyFlat_of_homeomorph_graph
    {E M F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [AddGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    {f : E → M} (hf : IsPLOn f (Set.univ : Set E)) (Φ : M ≃ₜ E × F)
    (hΦ : ∀ x, (Φ (f x)).1 = x) :
    IsLocallyFlat E F f :=
  (continuousOn_univ.mp hf.continuousOn).isLocallyFlat_of_homeomorph_graph Φ hΦ

end TauCeti
