/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Affine graphs are locally flat

The graph of a continuous affine map is locally flat, by the continuous-graph theorem in
`TauCeti.Geometry.Manifold.LocallyFlat.Basic`. The affine case is exposed in the
`ContinuousAffineMap` namespace for consumers building PL embeddings.

This is the graph building block for the locally flat embedding side of geometric topology.
-/

public section

namespace TauCeti

/-- The graph of a continuous affine map is locally flat, with complementary model `F`. -/
theorem _root_.ContinuousAffineMap.isLocallyFlat_affineGraph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →ᴬ[ℝ] F) :
    IsLocallyFlat E F (fun x : E => (x, A x)) :=
  TauCeti.isLocallyFlat_graph A A.continuous

end TauCeti
