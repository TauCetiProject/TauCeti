/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Isomorphism.Basic
public import TauCeti.Combinatorics.Graph.VertexCover.Basic

/-!
# Isomorphism invariance of vertex covers

A multigraph isomorphism transports sets of actual vertices by its vertex equivalence. This
transport preserves and reflects vertex covers.
-/

public section

open Set
open scoped Graph

universe u v u' v'

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {G : Graph α β} {H : Graph α' β'}

namespace Iso

/-- A graph isomorphism preserves and reflects vertex covers. -/
@[simp]
theorem isVertexCover_image_iff (f : Iso G H) (C : Set V(G)) :
    H.IsVertexCover (f.vertexEquiv '' C) ↔ G.IsVertexCover C := by
  rw [isVertexCover_iff_forall_exists_inc, isVertexCover_iff_forall_exists_inc,
    ← f.edgeEquiv.forall_congr_right]
  refine forall_congr' fun e ↦ ?_
  simp only [exists_mem_image, map_inc_iff]

end Iso

end Graph
