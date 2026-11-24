/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Pairing a field with a density of dual norm at most one

Let `F` be a real normed space and `τ : X → StrongDual ℝ F` a density with `‖τ x‖ ≤ 1` almost
everywhere. This file bounds the integral of the pairing `x ↦ τ x (f x)` of `τ` with a field
`f : X → F`:

* `TauCeti.enorm_integral_apply_le_lintegral_enorm`: `‖∫ τ x (f x) dμ‖ₑ ≤ ∫⁻ ‖f x‖ₑ dμ`;
* `TauCeti.lintegral_enorm_le_measure`: a field of norm at most one supported in a measurable set
  `U` has `∫⁻ ‖f x‖ₑ dμ ≤ μ U`;
* `TauCeti.enorm_integral_apply_le_measure`: for such a field, `‖∫ τ x (f x) dμ‖ₑ ≤ μ U`;
* `TauCeti.abs_integral_apply_le_mul_measureReal`: a field bounded by `c` and supported in a set
  `K` of finite measure has `|∫ τ x (f x) dμ| ≤ c μ(K)`;
* `CompactlySupportedContinuousMap.integrable_dual_apply`: for a compactly supported continuous
  field `f` and a measure finite on compact sets, the pairing is integrable.

These are the estimates behind the Riesz representation of functionals on `C_c(X, F)` by a measure
and a density of dual norm one.
-/

public section

open MeasureTheory Set
open scoped ENNReal CompactlySupported

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]

namespace TauCeti

/-- A density of dual norm at most one bounds its pairing with `f` by `∫ ‖f‖`. -/
theorem enorm_integral_apply_le_lintegral_enorm [NormedSpace ℝ F] {μ : Measure X}
    {τ : X → StrongDual ℝ F} (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1) (f : X → F) :
    ‖∫ x, τ x (f x) ∂μ‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono_ae (hτ.mono fun x hx => ?_))
  refine ((τ x).le_opENorm (f x)).trans (mul_le_of_le_one_left zero_le ?_)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hx

/-- A field of norm at most one supported in a measurable set `U` has `∫ ‖f‖ ≤ μ U`. -/
theorem lintegral_enorm_le_measure (μ : Measure X) {f : X → F} {U : Set X}
    (hU : MeasurableSet U) (hfU : Function.support f ⊆ U) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤ μ U := by
  rw [← lintegral_indicator_one hU]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx, Pi.one_apply, ← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 (hf x)
  · simp [Function.notMem_support.1 fun h => hx (hfU h)]

/-- The pairing of a field of norm at most one supported in a measurable set `U` with a density of
dual norm at most one is at most `μ U`. -/
theorem enorm_integral_apply_le_measure [NormedSpace ℝ F] {μ : Measure X}
    {τ : X → StrongDual ℝ F} (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1) {f : X → F} {U : Set X}
    (hU : MeasurableSet U) (hfU : Function.support f ⊆ U) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, τ x (f x) ∂μ‖ₑ ≤ μ U :=
  (enorm_integral_apply_le_lintegral_enorm hτ f).trans (lintegral_enorm_le_measure μ hU hfU hf)

/-- The pairing of a field bounded by `c` and supported in a measurable set `K` of finite measure
with a density of dual norm at most one is at most `c μ(K)`. -/
theorem abs_integral_apply_le_mul_measureReal [NormedSpace ℝ F] {μ : Measure X}
    {τ : X → StrongDual ℝ F} (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1) {K : Set X} (hK : MeasurableSet K)
    (hKμ : μ K ≠ ∞) {f : X → F} (hfK : Function.support f ⊆ K) {c : ℝ} (hf : ∀ x, ‖f x‖ ≤ c) :
    |∫ x, τ x (f x) ∂μ| ≤ c * μ.real K := by
  have hint : Integrable (K.indicator fun _ => c) μ :=
    (integrableOn_const hKμ).integrable_indicator hK
  rw [← Real.norm_eq_abs, mul_comm, ← smul_eq_mul, ← integral_indicator_const _ hK]
  refine norm_integral_le_of_norm_le hint (hτ.mono fun x hx => ?_)
  by_cases hxK : x ∈ K
  · rw [indicator_of_mem hxK]
    exact ((τ x).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hx).trans (hf x))
  · rw [indicator_of_notMem hxK, Function.notMem_support.1 fun h => hxK (hfK h), map_zero,
      norm_zero]

end TauCeti

namespace CompactlySupportedContinuousMap

variable [TopologicalSpace X] [OpensMeasurableSpace X] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The pairing of a compactly supported continuous field with a density of dual norm at most one
is integrable against a measure finite on compact sets. -/
theorem integrable_dual_apply (f : C_c(X, F)) {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {τ : X → StrongDual ℝ F} (hτm : AEStronglyMeasurable τ μ) (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1) :
    Integrable (fun x => τ x (f x)) μ :=
  (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm.mono'
    (Continuous.comp_aestronglyMeasurable₂ (g := fun (ℓ : StrongDual ℝ F) v => ℓ v) (by fun_prop)
      hτm f.continuous.aestronglyMeasurable)
    (hτ.mono fun x hx => ((τ x).le_opNorm (f x)).trans (mul_le_of_le_one_left (norm_nonneg _) hx))

end CompactlySupportedContinuousMap
