/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.ModelChange
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.RestrictScalars

/-!
# Changing the model of a compatible open gluing

Compatible overlap maps remain compatible after a continuous linear change of model coordinates
or restriction of scalars. In particular, holomorphic gluing gives the same underlying real
smooth manifold as gluing the underlying real pieces.

In both operations the chart spaces and their charted-space instances are unchanged. The named
atlas `TopCat.GlueData.chartedSpace` depends only on those instances and on the topological gluing
data, not on the scalar field or the model with corners. Thus it is literally the same atlas
before and after either operation, rather than a competing atlas on a new carrier.

Apply `TopCat.GlueData.IsCompatible.isManifold` to the resulting compatibility proof to obtain
the manifold structure. For a linear model change, Mathlib's
`ContinuousLinearEquiv.toTransContinuousLinearEquiv` supplies the identity comparison
diffeomorphism on the glued carrier, just as on each piece. The same theorem on local
diffeomorphisms also applies to the canonical inclusions and their local inverses.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Volume I, Chapter I.
* D. Huybrechts, *Complex Geometry: An Introduction*, Chapter 1 (underlying real manifolds).
-/

public section

open scoped Manifold ContDiff

namespace TopCat.GlueData

universe u

section LinearEquiv

variable (D : TopCat.GlueData.{u}) {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  [∀ i, ChartedSpace H (D.U i)] [∀ ij, ChartedSpace H (D.V ij)]

/-- Changing the vector-space coordinates of the model does not change compatibility of the
piece and overlap atlases. The gluing atlas itself is independent of these coordinates. -/
@[simp]
theorem isCompatible_transContinuousLinearEquiv_iff (e : E ≃L[𝕜] F) :
    D.IsCompatible (I.transContinuousLinearEquiv e) n ↔ D.IsCompatible I n := by
  simp only [isCompatible_iff,
    ContinuousLinearEquiv.isLocalDiffeomorph_transContinuousLinearEquiv_iff]

end LinearEquiv

section RestrictScalars

variable {D : TopCat.GlueData.{u}} (𝕜 : Type*) {𝕜' : Type*}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {n : ℕ∞ω}
  [∀ i, ChartedSpace E (D.U i)] [∀ ij, ChartedSpace E (D.V ij)]

/-- A compatible gluing for the trivial model over a normed field extension is compatible over
the smaller field, with unchanged piece, overlap, and glued atlases. In particular, a compatible
holomorphic gluing is a compatible smooth real gluing. -/
theorem IsCompatible.restrictScalars (h : D.IsCompatible 𝓘(𝕜', E) n) :
    D.IsCompatible 𝓘(𝕜, E) n where
  isLocalDiffeomorph_f i j := (h.isLocalDiffeomorph_f i j).restrictScalars 𝕜
  isLocalDiffeomorph_f_comp_t i j := (h.isLocalDiffeomorph_f_comp_t i j).restrictScalars 𝕜

end RestrictScalars

end TopCat.GlueData
