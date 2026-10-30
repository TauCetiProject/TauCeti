/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Integrals of test functions against measures finite on compact sets

Let `Ω` be an open set of a real normed space `E`. A test function `φ ∈ 𝓓^{n}(Ω, F)` restricts to
a compactly supported continuous function on the subspace `Ω`. For a test function `φ ∈ 𝓓(Ω, F)`
supported in a compact `K ⊆ Ω` and a measure `ν` on the subspace `Ω` that is finite on compact
sets, the integral of `φ` against `ν` is bounded by the sup norm:
`‖∫ φ dν‖ ≤ ν(K) ‖φ‖_∞`.

This is the estimate showing that integration against such a measure is a distribution of order
zero.

Every nonempty open subset of the domain also contains a nonnegative integral-one test, for any
locally finite measure positive on nonempty open sets. The construction normalizes Mathlib's
`exists_contDiff_tsupport_subset` by its positive integral. These tests recover the coefficient
of a constant distribution, including on arbitrarily small overlap neighborhoods.

## Main definitions

* `TestFunction.toCompactlySupportedContinuousMap`: the restriction of a test function on `Ω` to a
  compactly supported continuous function on the subspace `Ω`.

## Main results

* `TestFunction.exists_nonneg_integral_eq_one`: a nonnegative integral-one test supported in any
  nonempty open subset of the domain.

* `TestFunction.norm_integral_le_measureReal_mul_norm`: `‖∫ φ dν‖ ≤ ν(K) ‖φ‖_∞` for a test
  function `φ` supported in a compact `K ⊆ Ω`.
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions BoundedContinuousFunction CompactlySupported

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}

/-- The restriction of a test function on `Ω` to a compactly supported continuous function on the
subspace `Ω`. -/
def toCompactlySupportedContinuousMap (φ : 𝓓^{n}(Ω, F)) : C_c(Ω, F) where
  toFun x := φ x
  continuous_toFun := by fun_prop
  hasCompactSupport' := by
    refine HasCompactSupport.intro' (K := ((↑) : Ω → E) ⁻¹' tsupport φ) ?_
      ((isClosed_tsupport _).preimage continuous_subtype_val)
      fun x hx => image_eq_zero_of_notMem_tsupport hx
    exact Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage'
      φ.hasCompactSupport.isCompact (by simpa using φ.tsupport_subset)

@[simp]
theorem toCompactlySupportedContinuousMap_apply (φ : 𝓓^{n}(Ω, F)) (x : Ω) :
    φ.toCompactlySupportedContinuousMap x = φ x :=
  (rfl)

@[simp]
theorem toCompactlySupportedContinuousMap_zero :
    (0 : 𝓓^{n}(Ω, F)).toCompactlySupportedContinuousMap = 0 :=
  (rfl)

@[simp]
theorem toCompactlySupportedContinuousMap_add (φ ψ : 𝓓^{n}(Ω, F)) :
    (φ + ψ).toCompactlySupportedContinuousMap =
      φ.toCompactlySupportedContinuousMap + ψ.toCompactlySupportedContinuousMap :=
  (rfl)

@[simp]
theorem toCompactlySupportedContinuousMap_smul {R : Type*} [Semiring R] [Module R F]
    [SMulCommClass ℝ R F] [ContinuousConstSMul R F] (c : R) (φ : 𝓓^{n}(Ω, F)) :
    (c • φ).toCompactlySupportedContinuousMap = c • φ.toCompactlySupportedContinuousMap :=
  (rfl)

variable [MeasurableSpace E]

/-- The integral of a test function supported in a compact `K ⊆ Ω` against a measure on `Ω` that
is finite on compact sets is at most the measure of `K` times the sup norm. -/
theorem norm_integral_le_measureReal_mul_norm (φ : 𝓓(Ω, F)) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hφ : tsupport φ ⊆ K) (ν : Measure Ω) [IsFiniteMeasureOnCompacts ν] :
    ‖∫ x, φ x ∂ν‖ ≤ ν.real (((↑) : Ω → E) ⁻¹' K) * ‖(φ : E →ᵇ F)‖ := by
  have hK' : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK (by simpa using hKΩ)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ((↑) : Ω → E) ⁻¹' K)
    (f := fun x : Ω => φ x) fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hφ h),
    mul_comm]
  exact norm_setIntegral_le_of_norm_le_const hK'.measure_lt_top fun x _ => by
    simpa using (φ : E →ᵇ F).norm_coe_le_norm x

section IntegralOne

open Set
open scoped Topology

variable [FiniteDimensional ℝ E] [OpensMeasurableSpace E] {μ : Measure E}
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- There is a nonnegative integral-one test supported in any nonempty open subset of the
domain. The measure need not be translation invariant. -/
theorem exists_nonneg_integral_eq_one {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (hUΩ : U ⊆ Ω) :
    ∃ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U ∧ (∀ x, 0 ≤ φ x) ∧ ∫ x, φ x ∂μ = 1 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨f, hfs, hfc, hfd, hf01, hfx⟩ :=
    exists_contDiff_tsupport_subset (n := n) (hU.mem_nhds hx)
  have hfi : Integrable f μ := hfd.continuous.integrable_of_hasCompactSupport hfc
  have hf0 : ∀ y, 0 ≤ f y := fun y ↦ (hf01 (mem_range_self y)).1
  have hpos : 0 < ∫ y, f y ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero (x := x) hfd.continuous hfi hf0
      (by rw [hfx]; exact one_ne_zero)
  let φ : 𝓓^{n}(Ω, ℝ) := ⟨f, hfd, hfc, hfs.trans hUΩ⟩
  refine ⟨(∫ y, f y ∂μ)⁻¹ • φ, ?_, ?_, ?_⟩
  · simpa only [FunLike.coe_smul, Pi.smul_def, φ, coe_mk] using
      (tsupport_smul_subset_right (fun _ : E ↦ (∫ y, f y ∂μ)⁻¹) f).trans hfs
  · exact fun y ↦ mul_nonneg (inv_nonneg.mpr hpos.le) (hf0 y)
  · simp only [smul_apply, smul_eq_mul, φ, coe_mk, integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'

end IntegralOne

end TestFunction
