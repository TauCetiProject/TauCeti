/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Cover.Basic

/-!
# Triviality of the orientation double cover

A manifold is orientable if and only if its orientation double cover is a product with
`Fin 2` over the manifold. This holds without connectedness or separation assumptions, and
includes the empty manifold. The product homeomorphism sends its two sheets to the chosen
tangent orientations and their opposites, using the trivialization of the orientation cover
of an oriented vector bundle.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15, The Orientation Covering.
-/

public section

namespace TauCeti.Manifold.OrientationCover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [FiniteDimensional ℝ E]

/-- A manifold is orientable exactly when its orientation double cover is trivial over the
manifold. The homeomorphism must commute with the projections, and the manifold need not be
connected. -/
theorem orientable_iff_exists_homeomorph_orientationCover :
    Orientable I M ↔
      ∃ e : M × Fin 2 ≃ₜ OrientationCover I M, ∀ p, (e p).proj = p.1 := by
  rw [orientable_iff_nonempty_vectorBundleOrientation]
  constructor
  · rintro ⟨o⟩
    exact ⟨o.coverHomeomorph (Fintype.card_fin _), o.proj_coverHomeomorph _⟩
  · rintro ⟨e, he⟩
    exact (VectorBundleOrientation.nonempty_iff_exists_section (Fintype.card_fin _)).mpr
      ⟨fun x ↦ e (x, 0), e.continuous.comp (continuous_id.prodMk continuous_const),
        fun x ↦ he (x, 0)⟩

end TauCeti.Manifold.OrientationCover
