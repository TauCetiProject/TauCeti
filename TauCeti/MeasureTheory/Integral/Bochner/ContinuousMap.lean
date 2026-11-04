/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Bochner integration of continuous functions paired against integrable weights

On a compact topological space `X` equipped with a Borel-compatible measure `μ`, any continuous map
`f : C(X, E)` is bounded in the uniform norm and almost everywhere strongly measurable. Pairing `f`
through a continuous `𝕜`-bilinear map `B : E →L[𝕜] F →L[𝕜] G` with an `L¹` weight `g : X → F`
therefore produces an integrable integrand without assuming that `μ` is finite
(`ContinuousLinearMap.integrable_bilin_continuousMap_left`).

Sending `f` to `∫ x, B (f x) (g x) ∂μ` defines a continuous `𝕜`-linear operator
`ContinuousLinearMap.continuousMapIntegralCLM : C(X, E) →L[𝕜] G` of norm at most
`‖B‖ * ∫ x, ‖g x‖ ∂μ`. Composing this operator with uniform limits or formal multilinear series in
`C(X, E)` transports parameter expansions through weighted boundary integrals, such as surface
potentials on compact pieces of a piecewise smooth boundary.
-/

public section

open Filter MeasureTheory

namespace ContinuousLinearMap

section Integrable

variable {X 𝕜 E F G : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pairing a continuous map on a compact space with an integrable function through a continuous
bilinear map yields an integrable function, even when the ambient measure is infinite. -/
theorem integrable_bilin_continuousMap_left (B : E →L[𝕜] F →L[𝕜] G) (f : C(X, E))
    {g : X → F} (hg : Integrable g μ) :
    Integrable (fun x ↦ B (f x) (g x)) μ :=
  B.integrable_of_bilin_of_bdd_left ‖f‖ f.continuous.aestronglyMeasurable_of_compactSpace
    (Eventually.of_forall f.norm_coe_le_norm) hg

/-- Pairing an integrable function with a continuous map on a compact space through a continuous
bilinear map yields an integrable function. -/
theorem integrable_bilin_continuousMap_right (B : E →L[𝕜] F →L[𝕜] G) {f : X → E}
    (hf : Integrable f μ) (g : C(X, F)) :
    Integrable (fun x ↦ B (f x) (g x)) μ :=
  B.flip.integrable_bilin_continuousMap_left g hf

end Integrable

section IntegralCLM

variable {X 𝕜 E F G : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G]

/-- Weighted Bochner integration `f ↦ ∫ x, B (f x) (g x) ∂μ` on a compact space as a continuous
`𝕜`-linear map `C(X, E) →L[𝕜] G`. For an incomplete codomain `G`, Mathlib defines the Bochner
integral to be zero, so this operator is zero as well. -/
noncomputable def continuousMapIntegralCLM (B : E →L[𝕜] F →L[𝕜] G) {g : X → F}
    (hg : Integrable g μ) : C(X, E) →L[𝕜] G :=
  LinearMap.mkContinuous
    { toFun f := ∫ x, B (f x) (g x) ∂μ
      map_add' f₁ f₂ := by
        simp only [ContinuousMap.add_apply, map_add, add_apply]
        exact integral_add (B.integrable_bilin_continuousMap_left f₁ hg)
          (B.integrable_bilin_continuousMap_left f₂ hg)
      map_smul' c f := by
        simp only [ContinuousMap.smul_apply, map_smul, smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
    (‖B‖ * ∫ x, ‖g x‖ ∂μ) fun f ↦ by
      calc ‖∫ x, B (f x) (g x) ∂μ‖
        _ ≤ ∫ x, (‖B‖ * ‖f‖) * ‖g x‖ ∂μ :=
            norm_integral_le_of_norm_le (hg.norm.const_mul (‖B‖ * ‖f‖)) <|
              Eventually.of_forall fun x ↦ (B.le_opNorm₂ (f x) (g x)).trans <| by
                gcongr
                exact f.norm_coe_le_norm x
        _ = (‖B‖ * ∫ x, ‖g x‖ ∂μ) * ‖f‖ := by
            rw [integral_const_mul]
            ring

/-- Applying `B.continuousMapIntegralCLM hg` to `f` evaluates `∫ x, B (f x) (g x) ∂μ`. -/
@[simp]
theorem continuousMapIntegralCLM_apply (B : E →L[𝕜] F →L[𝕜] G) {g : X → F}
    (hg : Integrable g μ) (f : C(X, E)) :
    B.continuousMapIntegralCLM hg f = ∫ x, B (f x) (g x) ∂μ :=
  (rfl)

/-- The operator norm of `B.continuousMapIntegralCLM hg` is bounded by `‖B‖ * ∫ x, ‖g x‖ ∂μ`. -/
theorem norm_continuousMapIntegralCLM_le (B : E →L[𝕜] F →L[𝕜] G) {g : X → F}
    (hg : Integrable g μ) :
    ‖B.continuousMapIntegralCLM hg‖ ≤ ‖B‖ * ∫ x, ‖g x‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (norm_nonneg B) (integral_nonneg fun _ ↦ norm_nonneg _)) _

/-- Pairing through the zero bilinear map induces the zero integration operator. -/
@[simp]
theorem continuousMapIntegralCLM_zero_left {g : X → F} (hg : Integrable g μ) :
    (0 : E →L[𝕜] F →L[𝕜] G).continuousMapIntegralCLM hg = 0 := by
  ext f
  simp

/-- Pairing against the zero weight induces the zero integration operator. -/
@[simp]
theorem continuousMapIntegralCLM_zero_right (B : E →L[𝕜] F →L[𝕜] G) :
    B.continuousMapIntegralCLM (integrable_zero X F μ) = 0 := by
  ext f
  simp

end IntegralCLM

end ContinuousLinearMap
