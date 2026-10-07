/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic

/-!
# Barycentric membership in a precomplex polyhedron

A precomplex may omit vertices, as happens when a free vertex is removed by an elementary
collapse. Its coordinate polyhedron is still Mathlib's `Geometry.SimplicialComplex.onFinsupp`.
This file characterizes membership for a point of a closed coordinate simplex by its support.
It allows the geometric parts retained by a collapse to be read off from the deleted faces,
without adding unused vertices back to the complex.
-/

public section

open Set AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]

/-- A barycentric point belongs to the polyhedron of a precomplex exactly when its support
is a face of that precomplex. No assumption on the simplex containing the point is needed. -/
@[simp]
theorem mem_onFinsupp_space_iff (K : PreAbstractSimplicialComplex ι) {τ : Finset ι}
    (x : StandardSimplex τ) :
    x.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ↔ x.1.support ∈ K := by
  classical
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨ω, hω, hx⟩
    obtain ⟨ρ, hρ, rfl⟩ := hω
    let y : StandardSimplex ρ := ⟨x.1, by simpa only [Finset.coe_image] using hx⟩
    exact K.isRelLowerSet_faces.mem_of_le hρ (StandardSimplex.support_subset y)
      (Finsupp.support_nonempty_iff.mpr fun hz => by
        have hsum := StandardSimplex.sum_eq_one x
        simp [hz] at hsum)
  · intro hx
    exact ⟨x.1.support.image (fun v => Finsupp.single v (1 : ℝ)),
      ⟨x.1.support, hx, rfl⟩, by
        simpa only [Finset.coe_image] using StandardSimplex.mem_convexHull_support x⟩

end PreAbstractSimplicialComplex
