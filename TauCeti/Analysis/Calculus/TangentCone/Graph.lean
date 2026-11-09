/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Embedding
public import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Calculus.FDeriv.ImageCone

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
here identify the actual tangent space with the range used in that computation. Relative
differentiability also gives local pointwise containment in every cone about that range,
without finite-dimensionality or measure assumptions.
-/

public section

open Set Filter Metric
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

/-- Near the base point, a relatively differentiable normal graph lies in every cone about
the range of the derivative's linear graph. This holds in arbitrary real normed spaces,
without requiring the base point to belong to the parameter set. -/
theorem HasFDerivWithinAt.exists_pos_forall_infDist_range_normalGraphL_le
    (hφ : HasFDerivWithinAt φ A s x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ z ∈ TauCeti.normalGraphEmbedding φ '' s,
      dist z (TauCeti.normalGraphEmbedding φ x) < r →
        infDist (z - TauCeti.normalGraphEmbedding φ x)
            (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E))) ≤
          ε * dist z (TauCeti.normalGraphEmbedding φ x) := by
  -- Inserting the base point lets the inverse bound compare every parameter with it.
  have hi := (TauCeti.antilipschitzWith_normalGraphEmbedding φ).domRestrict (insert x s)
  obtain ⟨r, hr, hcone⟩ :=
    hφ.insert.normalGraphEmbedding.exists_pos_forall_infDist_range_le
      (mem_insert x s) hi hε
  exact ⟨r, hr, fun z hz => hcone z (image_mono (subset_insert x s) hz)⟩

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
