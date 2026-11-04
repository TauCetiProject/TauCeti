/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Integrals of test functions against measures finite on compact sets

Let `Ω` be an open set of a real normed space `E`. A test function `φ ∈ 𝓓^{n}(Ω, F)` restricts to
a compactly supported continuous function on the subspace `Ω`. For a test function `φ ∈ 𝓓(Ω, F)`
supported in a compact `K ⊆ Ω` and a measure `ν` on the subspace `Ω` that is finite on compact
sets, the integral of `φ` against `ν` is bounded by the sup norm:
`‖∫ φ dν‖ ≤ ν(K) ‖φ‖_∞`.

This is the estimate showing that integration against such a measure is a distribution of order
zero. Through a continuous bilinear map, a test function also pairs integrably with every
function that is locally integrable for a measure on `Ω`; in particular, integration against two
locally finite measures absolutely continuous with respect to `ρ` is integration against their
Radon–Nikodym derivatives with respect to `ρ`.

Every nonempty open subset of the domain also contains a nonnegative integral-one test, for any
locally finite measure positive on nonempty open sets. The construction normalizes Mathlib's
`exists_contDiff_tsupport_subset` by its positive integral. These tests recover the coefficient
of a constant distribution, including on arbitrarily small overlap neighborhoods.

Against an additive Haar measure, the directional derivative of a test function has integral
zero, by Mathlib's integration by parts against the constant function `1`.

## Main definitions

* `TestFunction.toCompactlySupportedContinuousMap`: the restriction of a test function on `Ω` to a
  compactly supported continuous function on the subspace `Ω`.

## Main results

* `TestFunction.exists_nonneg_integral_eq_one`: a nonnegative integral-one test supported in any
  nonempty open subset of the domain.

* `TestFunction.norm_integral_le_measureReal_mul_norm`: `‖∫ φ dν‖ ≤ ν(K) ‖φ‖_∞` for a test
  function `φ` supported in a compact `K ⊆ Ω`.

* `TestFunction.lintegral_enorm_le_mul_measure_preimage`: `∫ ‖φ‖ dν ≤ a ν(U)` for a test
  function `φ` supported in `U` with `‖φ‖ ≤ a`.

* `TestFunction.integrable_bilin_subtype`: `x ↦ B (φ x) (g x)` is integrable for `g` locally
  integrable for a measure on `Ω`.

* `TestFunction.integrable_apply_of_locallyIntegrable`: `x ↦ τ(x) (φ x)` is integrable for a
  locally integrable field `τ` of continuous linear maps.

* `TestFunction.integral_sub_integral_eq_integral_mul_sub_rnDeriv`: integration against two
  locally finite measures as integration against their densities with respect to a reference
  measure.

* `TestFunction.integral_lineDeriv_eq_zero`: `∫ ∂_w φ dμ = 0` for an additive Haar measure `μ`.
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions BoundedContinuousFunction CompactlySupported ENNReal

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

/-- A test function supported in `U` with `‖φ‖ ≤ a` has `∫ ‖φ‖ dν ≤ a ν(Ω ∩ U)`. -/
theorem lintegral_enorm_le_mul_measure_preimage (φ : 𝓓^{n}(Ω, F)) (ν : Measure Ω) {U : Set E}
    (hU : MeasurableSet U) (hφU : tsupport φ ⊆ U) {a : ℝ≥0∞} (hφ : ∀ x, ‖φ x‖ₑ ≤ a) :
    ∫⁻ x, ‖φ x‖ₑ ∂ν ≤ a * ν ((↑) ⁻¹' U) := by
  rw [← lintegral_indicator_const (measurable_subtype_coe hU)]
  refine lintegral_mono fun x => ?_
  by_cases hx : (x : E) ∈ U
  · simpa [Set.indicator_of_mem (Set.mem_preimage.2 hx)] using hφ x
  · simp [Set.indicator_of_notMem fun h => hx (Set.mem_preimage.1 h),
      image_eq_zero_of_notMem_tsupport fun h => hx (hφU h)]

/-- A test function on `Ω` pairs integrably, through a continuous bilinear map `B`, with every
function `g` that is locally integrable for a measure on the subspace `Ω`. -/
theorem integrable_bilin_subtype [OpensMeasurableSpace E] {F₂ F₃ : Type*} [NormedAddCommGroup F₂]
    [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] (B : F →L[ℝ] F₂ →L[ℝ] F₃)
    {ν : Measure Ω} {g : Ω → F₂} (hg : LocallyIntegrable g ν) (φ : 𝓓^{n}(Ω, F)) :
    Integrable (fun x : Ω => B (φ x) (g x)) ν := by
  set f := φ.toCompactlySupportedContinuousMap
  have hf : (f : Ω → F) = fun x : Ω => φ x := funext (toCompactlySupportedContinuousMap_apply φ)
  have hK : IsCompact (tsupport f) := f.hasCompactSupport
  have hon : IntegrableOn (fun x => B (f x) (g x)) (tsupport f) ν := by
    rw [IntegrableOn, ← memLp_one_iff_integrable]
    exact B.memLp_of_bilin 1 (f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport _)
      (memLp_one_iff_integrable.2 (hg.integrableOn_isCompact hK))
  rw [hf] at hon
  refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).1 hon
  exact subset_tsupport _ fun hφx => hx (by simp [(congrFun hf x).symm.trans hφx])

/-- The pairing `x ↦ τ(x) (φ x)` of a test function `φ` on `Ω` with a field `τ` of continuous
linear maps on `F`, locally integrable for a measure on the subspace `Ω`, is integrable. -/
theorem integrable_apply_of_locallyIntegrable [OpensMeasurableSpace E] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {ν : Measure Ω} {τ : Ω → F →L[ℝ] G}
    (hτ : LocallyIntegrable τ ν) (φ : 𝓓^{n}(Ω, F)) : Integrable (fun x => τ x (φ x)) ν :=
  integrable_bilin_subtype (ContinuousLinearMap.apply ℝ G) hτ φ

/-- Integration of a test function against the difference of two locally finite measures `ν₁` and
`ν₂`, absolutely continuous with respect to `ρ`, is integration against the difference of their
Radon–Nikodym derivatives with respect to `ρ`. -/
theorem integral_sub_integral_eq_integral_mul_sub_rnDeriv [FiniteDimensional ℝ E] [BorelSpace E]
    {ν₁ ν₂ ρ : Measure Ω} [IsLocallyFiniteMeasure ν₁] [IsLocallyFiniteMeasure ν₂]
    [SigmaFinite ρ] (h₁ : ν₁ ≪ ρ) (h₂ : ν₂ ≪ ρ) (ψ : 𝓓(Ω, ℝ)) :
    ∫ x, ψ x ∂ν₁ - ∫ x, ψ x ∂ν₂ =
      ∫ x, ψ x * ((ν₁.rnDeriv ρ x).toReal - (ν₂.rnDeriv ρ x).toReal) ∂ρ := by
  have hint (ν : Measure Ω) [IsLocallyFiniteMeasure ν] :
      Integrable (fun x => (ν.rnDeriv ρ x).toReal * ψ x) ρ :=
    (ψ.integrable_bilin_subtype (ContinuousLinearMap.mul ℝ ℝ)
      (Measure.locallyIntegrable_toReal_rnDeriv (μ := ν))).congr
        (ae_of_all _ fun x => by simp [mul_comm])
  rw [← integral_toReal_rnDeriv_mul h₁, ← integral_toReal_rnDeriv_mul h₂,
    ← integral_sub (hint ν₁) (hint ν₂)]
  congr with x
  ring

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
    MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (x := x) hfd.continuous hfi hf0
      (by rw [hfx]; exact one_ne_zero)
  let φ : 𝓓^{n}(Ω, ℝ) := ⟨f, hfd, hfc, hfs.trans hUΩ⟩
  refine ⟨(∫ y, f y ∂μ)⁻¹ • φ, ?_, ?_, ?_⟩
  · simpa only [FunLike.coe_smul, Pi.smul_def, φ, coe_mk] using
      (tsupport_smul_subset_right (fun _ : E ↦ (∫ y, f y ∂μ)⁻¹) f).trans hfs
  · exact fun y ↦ mul_nonneg (inv_nonneg.mpr hpos.le) (hf0 y)
  · simp only [_root_.smul_apply, smul_eq_mul, φ, coe_mk, integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'

end IntegralOne

section LineDeriv

variable [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The directional derivative of a test function has integral zero against an additive Haar
measure: `∫ ∂_w φ = 0`. -/
theorem integral_lineDeriv_eq_zero (φ : 𝓓(Ω, ℝ)) (w : E) :
    ∫ x, lineDeriv ℝ (φ : E → ℝ) x w ∂μ = 0 := by
  have hd := φ.contDiff.differentiable (by simp)
  have hint (ψ : 𝓓(Ω, ℝ)) : Integrable ψ μ :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hφ' : ⇑(lineDerivCLM ℝ w φ : 𝓓(Ω, ℝ)) = fun x ↦ lineDeriv ℝ φ x w :=
    funext fun _ ↦ lineDerivCLM_apply_of_le le_top
  -- Integrating by parts against the constant function `1`.
  simpa using integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := μ)
    (f := fun _ ↦ (1 : ℝ)) (f' := fun _ ↦ 0) (g := φ) (g' := fun x ↦ lineDeriv ℝ φ x w)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (by simp)
    (by simpa [hφ'] using hint (lineDerivCLM ℝ w φ)) (by simpa using hint φ)
    (fun x _ ↦ by simpa using (hasFDerivAt_const (1 : ℝ) x).hasLineDerivAt w)
    fun x _ ↦ (hd x).lineDifferentiableAt.hasLineDerivAt

end LineDeriv

end TestFunction
