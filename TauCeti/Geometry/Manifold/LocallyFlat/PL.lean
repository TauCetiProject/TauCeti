/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Topology.PL.Map
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Piecewise-linear graphs are locally flat

The graph of a continuous map is locally flat, by the continuous-graph theorem in
`TauCeti.Geometry.Manifold.LocallyFlat.Basic`. This file combines that result with the
piecewise-linear continuity theorem, and retains the affine specialization in the
`ContinuousAffineMap` namespace for consumers building PL embeddings.

This is the graph building block for the locally flat embedding side of geometric topology. The
non-affine statement applies, for example, to the absolute-value PL map. The graph-chart
criterion below transports this local model through an ambient homeomorphism.
-/

public section

namespace TauCeti

/-- A map piecewise linear on all of `E` has a locally flat graph `x ↦ (x, f x)` with
complementary model `F`. -/
theorem IsPLOn.isLocallyFlat_graph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : IsPLOn f (Set.univ : Set E)) :
    IsLocallyFlat E F (fun x : E => (x, f x)) := by
  apply TauCeti.isLocallyFlat_graph f
  exact continuousOn_univ.mp hf.continuousOn

/-- The graph of a continuous affine map is locally flat, with complementary model `F`. -/
theorem _root_.ContinuousAffineMap.isLocallyFlat_affineGraph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →ᴬ[ℝ] F) :
    IsLocallyFlat E F (fun x : E => (x, A x)) :=
  (isPLOn_continuousAffineMap A (Set.univ : Set E)).isLocallyFlat_graph

/-- A globally PL map is locally flat when an ambient homeomorphism presents its image as a
graph.  The section equation on the first coordinate is the only compatibility needed: PL
regularity supplies continuity of the graph function, and the existing graph theorem then
transports local flatness through the ambient homeomorphism. -/
theorem IsPLOn.isLocallyFlat_of_homeomorph_graph
    {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup F]
    {f : E → M} (hf : IsPLOn f (Set.univ : Set E)) (Φ : M ≃ₜ E × F)
    (hΦ : ∀ x, (Φ (f x)).1 = x) :
    IsLocallyFlat E F f := by
  let g : E → F := fun x => (Φ (f x)).2
  have hg : Continuous g := by
    apply continuous_snd.comp
    exact Φ.continuous.comp (continuousOn_univ.mp hf.continuousOn)
  have hgraph : IsLocallyFlat E F (fun x => (x, g x)) :=
    TauCeti.isLocallyFlat_graph g hg
  have htransport := hgraph.homeomorph_comp Φ.symm
  convert htransport using 1
  funext x
  apply Φ.injective
  rw [Function.comp_apply, Φ.apply_symm_apply]
  exact Prod.ext (hΦ x) rfl

end TauCeti
