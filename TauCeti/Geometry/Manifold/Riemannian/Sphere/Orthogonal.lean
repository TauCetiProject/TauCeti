/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic

/-!
# Stabilizers of points on the round sphere

A reflection in the orthogonal complement of the difference of two tangent vectors of equal
length exchanges those vectors while fixing their base point on the unit sphere.

## Main result

* `TauCeti.Manifold.exists_linearIsometryEquiv_fix_mvfderiv`: the stabilizer of a point in the
  orthogonal group acts transitively on tangent vectors of a given length.

The smooth isometric action of the orthogonal group, its differential, and transitivity on sphere
points are already in `TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic`.
-/

public section

open Bundle Manifold Metric Module
open scoped InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The stabilizer of a point acts transitively on tangent vectors of a given length: a reflection
fixes the point and exchanges the vectors when read in the ambient space. -/
theorem exists_linearIsometryEquiv_fix_mvfderiv (x : sphere (0 : E) 1)
    {u u' : TangentSpace (𝓡 n) x} (h : ‖u‖ = ‖u'‖) :
    ∃ e : E ≃ₗᵢ[ℝ] E, e x = x ∧
      e (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x u) =
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x u' := by
  refine ⟨Submodule.reflection (ℝ ∙ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x u -
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x u'))ᗮ, ?_, ?_⟩
  · apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_left,
      real_inner_comm (x : E), real_inner_comm (x : E), inner_coe_mvfderiv_subtypeVal_sphere,
      inner_coe_mvfderiv_subtypeVal_sphere, sub_zero]
  · apply Submodule.reflection_sub
    rw [← norm_tangentSpace_sphere x u, ← norm_tangentSpace_sphere x u']
    exact h

end TauCeti.Manifold
