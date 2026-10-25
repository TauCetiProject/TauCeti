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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals of continuous functions on a compact space

On a compact space `X`, every continuous function is integrable against a finite measure
(`ContinuousMap.integrable`), and integration against a finite measure is Lipschitz, hence
continuous, in the integrand for the sup norm on `C(X, E)`. This is what lets an identity between
integrals pass from a dense subset of `C(X, E)` to all of it.

For `𝕜 = ℝ` or `ℂ`, integration against a finite measure is a positive linear functional on
`C(X, 𝕜)` (`ContinuousMap.integralPositiveLinearMap`), the compact-space, `𝕜`-valued counterpart of
Mathlib's `CompactlySupportedContinuousMap.integralPositiveLinearMap`. For `𝕜 = ℂ` it is a positive
functional on the commutative C⋆-algebra `C(X, ℂ)`, and a state when the measure is a probability
measure.

A `𝕜`-linear functional on `C(X, 𝕜)` that agrees with integration on real functions agrees with it
everywhere (`LinearMap.apply_eq_integral_of_forall_realToRCLike`), since every `f : C(X, 𝕜)` is
`re f + i im f`. This turns a Riesz–Markov–Kakutani measure of a real positive functional into a
representation of its complexification.
-/

public section

open MeasureTheory Set
open scoped ComplexOrder

/-- On a compact space, a continuous function is integrable against every finite measure. -/
theorem ContinuousMap.integrable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E] (f : C(X, E))
    (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (.of_compactSpace _)

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
