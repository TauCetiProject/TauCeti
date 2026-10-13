/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Moving a point of the unit sphere by a reflection

Any point of the unit sphere of a real inner product space is carried to any other by the
reflection in the hyperplane orthogonal to their difference. This restricts to a homeomorphism of
the sphere.

## Main declarations

* `TauCeti.sphereHomeomorphOfBasepoints`: the reflection as a homeomorphism of the unit sphere.
* `TauCeti.sphereHomeomorphOfBasepoints_apply_self`: it carries the first point to the second.
-/

public section

noncomputable section

open Metric Submodule

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Any point of the unit sphere is carried to any other by a homeomorphism of the sphere: the
reflection in the hyperplane orthogonal to the difference. -/
def sphereHomeomorphOfBasepoints (v w : sphere (0 : E) 1) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  (reflection (ℝ ∙ ((v : E) - w))ᗮ).toHomeomorph.subtype fun x => by
    simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph,
      LinearIsometryEquiv.norm_map]

omit [FiniteDimensional ℝ E] in
theorem sphereHomeomorphOfBasepoints_apply_self (v w : sphere (0 : E) 1) :
    sphereHomeomorphOfBasepoints v w v = w :=
  Subtype.ext (reflection_sub (by simp [mem_sphere_zero_iff_norm.1 v.2,
    mem_sphere_zero_iff_norm.1 w.2]))

end TauCeti
