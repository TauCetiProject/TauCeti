/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Embedding
public import TauCeti.Analysis.Calculus.FDeriv.WithLp

/-!
# Tangent spaces of normal graphs

At a differentiability point of a real function, the tangent cone to its normal graph is
exactly the linear graph of its derivative. More generally, relative differentiability
transports the tangent cone of any parameter set by the linear graph of the derivative.
For a neighborhood of the parameter this image is the full linear graph. Thus the cone is
already a linear space, and its span has the dimension of the parameter space. No continuous
derivative is needed.

The parametrization is `TauCeti.normalGraphEmbedding` in the Euclidean product
`WithLp 2 (ℝ × E)`. Its Jacobian is computed in `Analysis.Calculus.FDeriv.WithLp`; the results
here identify the actual tangent space with the range used in that computation.
-/

public section

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {φ : E → ℝ} {A : E →L[ℝ] ℝ} {x : E} {s : Set E}

/-- Relative differentiability transports the tangent cone of the parameter set to the
normal graph by the linear graph of the derivative. -/
theorem HasFDerivWithinAt.tangentConeAt_normalGraphEmbedding_image
    (hφ : HasFDerivWithinAt φ A s x) :
    tangentConeAt ℝ (TauCeti.normalGraphEmbedding φ '' s) (TauCeti.normalGraphEmbedding φ x) =
      A.normalGraphL '' tangentConeAt ℝ s x :=
  (hφ.normalGraphEmbedding.image_tangentConeAt_of_leftInverse
    (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt.hasFDerivWithinAt
    (TauCeti.normalGraphEmbedding_snd φ)).symm

namespace HasFDerivAt

/-- The tangent cone of a differentiable normal graph, restricted to a neighborhood of the
parameter, is the range of the linear graph of the derivative. This holds in arbitrary real
normed spaces, without a continuous derivative hypothesis. -/
theorem tangentConeAt_normalGraphEmbedding_image (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    tangentConeAt ℝ (TauCeti.normalGraphEmbedding φ '' s) (TauCeti.normalGraphEmbedding φ x) =
      (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E))) := by
  rw [hφ.hasFDerivWithinAt.tangentConeAt_normalGraphEmbedding_image,
    tangentConeAt_of_mem_nhds hs, image_univ]
  simp only [LinearMap.coe_range, ContinuousLinearMap.coe_coe]

/-- The classical tangent space of a differentiable normal graph is the range of the
differential of its parametrization. -/
theorem span_tangentConeAt_normalGraphEmbedding_image (hφ : HasFDerivAt φ A x)
    (hs : s ∈ 𝓝 x) :
    Submodule.span ℝ
      (tangentConeAt ℝ (TauCeti.normalGraphEmbedding φ '' s) (TauCeti.normalGraphEmbedding φ x)) =
      LinearMap.range A.normalGraphL.toLinearMap := by
  rw [hφ.tangentConeAt_normalGraphEmbedding_image hs, Submodule.span_eq]

/-- The tangent space of a differentiable normal graph has the dimension of its parameter
space. In particular, a graph over a `k`-dimensional space has a classical tangent `k`-plane. -/
theorem finrank_span_tangentConeAt_normalGraphEmbedding_image (hφ : HasFDerivAt φ A x)
    (hs : s ∈ 𝓝 x) :
    Module.finrank ℝ (Submodule.span ℝ
      (tangentConeAt ℝ (TauCeti.normalGraphEmbedding φ '' s) (TauCeti.normalGraphEmbedding φ x))) =
      Module.finrank ℝ E := by
  rw [hφ.span_tangentConeAt_normalGraphEmbedding_image hs]
  exact LinearMap.finrank_range_of_inj A.injective_normalGraphL

end HasFDerivAt
