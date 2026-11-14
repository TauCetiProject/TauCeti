/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Vertices of concatenated quiver paths

Membership in the vertex list of a concatenated quiver path `p.comp q` is membership in the vertex
list of `p` or of `q`, since the common meeting vertex ends `p` and starts `q`.
-/

public section

namespace Quiver.Path

universe u v

variable {V : Type u} [Quiver.{v} V]

/-- A vertex lies on a concatenated path `p.comp q` if and only if it lies on `p` or on `q`. -/
@[simp]
theorem mem_vertices_comp {a b c : V} (p : Path a b) (q : Path b c) {v : V} :
    v ∈ (p.comp q).vertices ↔ v ∈ p.vertices ∨ v ∈ q.vertices := by
  rw [vertices_comp, List.mem_append]
  conv_rhs => rw [← p.dropLast_append_end_eq, List.mem_append, List.mem_singleton]
  refine ⟨by tauto, ?_⟩
  rintro ((hv | rfl) | hv)
  · exact .inl hv
  · exact .inr q.start_mem_vertices
  · exact .inr hv

end Quiver.Path
