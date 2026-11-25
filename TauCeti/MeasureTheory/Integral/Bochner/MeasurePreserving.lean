/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals of inner products moved by a measure-preserving map

Moving two functions `v` and `w` by a measure-preserving measurable embedding `g` and their values
by a linear isometry `R` preserves the integral of their pointwise inner product: the integral of
`⟪(R ∘ v ∘ g) z, (R ∘ w ∘ g) z⟫` against `μ` is that of `⟪v z, w z⟫` against `ν`
(`MeasureTheory.MeasurePreserving.integral_inner_comp_comp`). No integrability is needed, since
the change of variables `MeasureTheory.MeasurePreserving.integral_comp` holds for every integrand.
Functions given by almost-everywhere representatives, such as `L²` classes, are handled by
`MeasureTheory.integral_congr_ae` at the call site.
-/

public section

open scoped InnerProductSpace

namespace MeasureTheory

variable {α β 𝕜 E F : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Change of variables for an inner-product pairing.** Moving both functions by a
measure-preserving measurable embedding `g` and their values by a linear isometry `R` preserves the
integral of their pointwise inner product. -/
theorem MeasurePreserving.integral_inner_comp_comp {g : α → β} (hg : MeasurePreserving g μ ν)
    (hge : MeasurableEmbedding g) (R : E →ₗᵢ[𝕜] F) (v w : β → E) :
    ∫ z, ⟪(R ∘ v ∘ g) z, (R ∘ w ∘ g) z⟫_𝕜 ∂μ = ∫ z, ⟪v z, w z⟫_𝕜 ∂ν := by
  simp only [Function.comp_apply, LinearIsometry.inner_map_map]
  exact hg.integral_comp hge fun z ↦ ⟪v z, w z⟫_𝕜

end MeasureTheory
