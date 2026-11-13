/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.RCLike.ContinuousMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals of continuous functions on a compact space

On a compact space `X`, every continuous function is integrable against a finite measure
(`Continuous.integrable_of_compactSpace`, `ContinuousMap.integrable`), as is its product with an
integrable function against any measure (`MeasureTheory.Integrable.mul_continuous_of_compactSpace`),
and integration against a finite measure is Lipschitz, hence continuous, in the integrand for the
sup norm on `C(X, E)`. This is what lets an identity between integrals pass from a dense subset of
`C(X, E)` to all of it.

For `𝕜 = ℝ` or `ℂ`, integration against a finite measure is a positive linear functional on
`C(X, 𝕜)` (`ContinuousMap.integralPositiveLinearMap`), the compact-space, `𝕜`-valued counterpart of
Mathlib's `CompactlySupportedContinuousMap.integralPositiveLinearMap`. For `𝕜 = ℂ` it is a positive
functional on the commutative C⋆-algebra `C(X, ℂ)`, and a state when the measure is a probability
measure.

A `𝕜`-linear functional on `C(X, 𝕜)` that agrees with integration on real functions agrees with it
everywhere (`LinearMap.apply_eq_integral_of_forall_realToRCLike`), since every `f : C(X, 𝕜)` is
`re f + i im f`. This turns a Riesz–Markov–Kakutani measure of a real positive functional into a
representation of its complexification.

More generally, pairing `f : C(X, E)` through a continuous `𝕜`-bilinear map
`B : E →L[𝕜] F →L[𝕜] G` with an `L¹` weight `g : X → F` produces an integrable integrand against
any Borel-compatible measure `μ` (`ContinuousLinearMap.integrable_bilin_continuousMap_left`), and
`f ↦ ∫ x, B (f x) (g x) ∂μ` defines a continuous `𝕜`-linear operator
`ContinuousLinearMap.continuousMapIntegralCLM : C(X, E) →L[𝕜] G` of norm at most
`‖B‖ * ∫ x, ‖g x‖ ∂μ`.
-/

public section

open MeasureTheory Set
open scoped ComplexOrder

section Integrable

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- On a compact space, a continuous function is integrable against every finite measure. -/
theorem Continuous.integrable_of_compactSpace {E : Type*} [NormedAddCommGroup E] {f : X → E}
    (hf : Continuous f) {μ : Measure X} [IsFiniteMeasure μ] : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- On a compact space, a continuous function is integrable against every finite measure. -/
theorem ContinuousMap.integrable {E : Type*} [NormedAddCommGroup E] (f : C(X, E))
    (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ :=
  f.continuous.integrable_of_compactSpace

/-- On a compact space, the product of an integrable function with a continuous function is
integrable. -/
theorem MeasureTheory.Integrable.mul_continuous_of_compactSpace {𝕜 : Type*} [NormedRing 𝕜]
    {φ f : X → 𝕜} {μ : Measure X} (hφ : Integrable φ μ) (hf : Continuous f) :
    Integrable (fun x ↦ φ x * f x) μ :=
  hφ.mul_of_top_left (hf.memLp_top_of_hasCompactSupport (.of_compactSpace _) μ)

end Integrable

section integralPositiveLinearMap

variable {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [IsFiniteMeasure μ]

/-- Integration against a finite measure on a compact space, as a positive linear functional on
`C(X, 𝕜)`. -/
noncomputable def ContinuousMap.integralPositiveLinearMap : C(X, 𝕜) →ₚ[𝕜] 𝕜 :=
  PositiveLinearMap.mk₀
    { toFun f := ∫ x, f x ∂μ
      map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
      map_smul' c f := integral_smul c f }
    fun _ hf ↦ integral_nonneg fun x ↦ hf x

/-- `ContinuousMap.integralPositiveLinearMap μ` integrates against `μ`. -/
@[simp]
theorem ContinuousMap.integralPositiveLinearMap_apply (f : C(X, 𝕜)) :
    integralPositiveLinearMap μ f = ∫ x, f x ∂μ := by
  rw [integralPositiveLinearMap, PositiveLinearMap.mk₀]
  rfl

/-- Integration against `μ` sends the constant function `1` to the total mass of `μ`, so it is a
state exactly when `μ` is a probability measure. -/
theorem ContinuousMap.integralPositiveLinearMap_one :
    integralPositiveLinearMap μ (1 : C(X, 𝕜)) = (μ.real univ : 𝕜) := by
  simp [integral_const, RCLike.real_smul_eq_coe_mul]

end integralPositiveLinearMap

/-- On a compact space, a `𝕜`-linear functional `φ` on `C(X, 𝕜)` that agrees with integration
against a finite measure `μ` on real functions is integration against `μ`. -/
theorem LinearMap.apply_eq_integral_of_forall_realToRCLike {X 𝕜 : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [RCLike 𝕜]
    (φ : C(X, 𝕜) →ₗ[𝕜] 𝕜) {μ : Measure X} [IsFiniteMeasure μ]
    (h : ∀ g : C(X, ℝ), φ (g.realToRCLike 𝕜) = ((∫ x, g x ∂μ : ℝ) : 𝕜)) (f : C(X, 𝕜)) :
    φ f = ∫ x, f x ∂μ := by
  -- Split `f` into its real and imaginary parts, and apply the real case to each.
  let u : C(X, ℝ) := ⟨fun x ↦ RCLike.re (f x), by fun_prop⟩
  let v : C(X, ℝ) := ⟨fun x ↦ RCLike.im (f x), by fun_prop⟩
  have hf : f = u.realToRCLike 𝕜 + (RCLike.I : 𝕜) • v.realToRCLike 𝕜 := by
    ext x
    simp [u, v, mul_comm RCLike.I]
  rw [← integral_re_add_im (f.integrable μ)]
  nth_rw 1 [hf]
  rw [map_add, map_smul, h, h, smul_eq_mul, mul_comm]
  rfl

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a compact space, integration against a finite measure is a continuous function of the
integrand for the topology of uniform convergence on `C(X, E)`. -/
theorem continuous_integral_continuousMap {μ : Measure X} [IsFiniteMeasure μ] :
    Continuous fun f : C(X, E) ↦ ∫ x, f x ∂μ := by
  refine (LipschitzWith.of_dist_le_mul (K := (μ.real univ).toNNReal) fun f g ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ measureReal_nonneg, mul_comm,
    ← integral_sub (f.integrable μ) (g.integrable μ)]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ (f - g).norm_coe_le_norm x)

end TauCeti

namespace ContinuousLinearMap

open Filter

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
