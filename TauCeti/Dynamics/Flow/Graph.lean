/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.Topology.Algebra.Module.ProjectionGraph

/-!
# Transporting graphs along a flow

A graph over the range of an idempotent continuous linear map is embedded. Each fixed-time map of
a flow with time in an additive group is a homeomorphism, so translating such a graph and
transporting it along the flow keeps it embedded. This is the topological part of transporting
local stable and unstable disks along orbits.

## Main declarations

* `Flow.isEmbedding_graph`: flowing a graph over the range of an idempotent continuous linear map
  gives another topological embedding.
-/

public section

open Topology

namespace Flow

variable {τ R E : Type*} [TopologicalSpace τ] [AddGroup τ] [Semiring R]
  [TopologicalSpace E] [AddCommGroup E] [ContinuousAdd E] [Module R E]

/-- A graph over the range of an idempotent continuous linear map remains embedded after
translation and transport by any fixed time of a flow. -/
theorem isEmbedding_graph (φ : Flow τ E) (P : E →L[R] E) (hP : IsIdempotentElem P)
    (g : E → E) (hPg : ∀ v ∈ P.range, P (g v) = 0) (hg : ContinuousOn g P.range)
    (x : E) (t : τ) :
    IsEmbedding (fun v : P.range ↦ φ t (x + ((v : E) + g (v : E)))) := by
  have hgraph : IsEmbedding (fun v : P.range ↦ (v : E) + g (v : E)) :=
    P.isEmbedding_graph hP g hPg hg
  simpa only [Homeomorph.coe_addLeft, Function.comp_def, toHomeomorph_apply] using
    (φ.toHomeomorph t).isEmbedding.comp
      ((Homeomorph.addLeft x).isEmbedding.comp hgraph)

end Flow
