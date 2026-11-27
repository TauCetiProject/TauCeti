/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import TauCeti.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.ENorm

/-!
# Integrals of test functions against measures finite on compact sets

Let `Ω` be an open set of a real normed space `E`. A test function `φ ∈ 𝓓^{n}(Ω, F)` restricts to
a compactly supported continuous function on the subspace `Ω`. For a test function `φ ∈ 𝓓(Ω, F)`
supported in a compact `K ⊆ Ω` and a measure `ν` on the subspace `Ω` that is finite on compact
sets, the integral of `φ` against `ν` is bounded by the sup norm:
`‖∫ φ dν‖ ≤ ν(K) ‖φ‖_∞`.

This is the estimate showing that integration against such a measure is a distribution of order
zero. Through a continuous bilinear map, a test function also pairs integrably with every
function that is locally integrable for a measure on `Ω`.

Every nonempty open subset of the domain also contains a nonnegative integral-one test, for any
locally finite measure positive on nonempty open sets. The construction normalizes Mathlib's
`exists_contDiff_tsupport_subset` by its positive integral. These tests recover the coefficient
of a constant distribution, including on arbitrarily small overlap neighborhoods.

Against an additive Haar measure, the directional derivative of a test function has integral
zero, by Mathlib's integration by parts against the constant function `1`.

On a finite-dimensional space, against a locally finite measure positive on nonempty open sets, a
function continuous on an open set is determined there by its integrals against smooth compactly
supported functions, by Mathlib's fundamental lemma of the calculus of variations
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. In particular a test function is determined
by these integrals.

## Main definitions

* `TestFunction.toCompactlySupportedContinuousMap`: the restriction of a test function on `Ω` to a
  compactly supported continuous function on the subspace `Ω`.

## Main results

* `TestFunction.coe_extendZero_toCompactlySupportedContinuousMap`: extending this restriction by
  zero (`CompactlySupportedContinuousMap.extendZero`) recovers the test function.

* `TestFunction.exists_nonneg_integral_eq_one`: a nonnegative integral-one test supported in any
  nonempty open subset of the domain.

* `TestFunction.norm_integral_le_measureReal_mul_norm`: `‖∫ φ dν‖ ≤ ν(K) ‖φ‖_∞` for a test
  function `φ` supported in a compact `K ⊆ Ω`.

* `TestFunction.integrable_bilin_subtype`: `x ↦ B (φ x) (g x)` is integrable for `g` locally
  integrable for a measure on `Ω`.

* `TestFunction.neg_integral_smul_neg_add_eq`: the integral of a test function against the
  right-hand side `-(f + ∑ᵢⱼ Gᵢⱼ)` of a weak derivative equation.

* `TestFunction.integral_smul_congr_of_eqOn`: `∫ φ • g₁ ∂μ = ∫ φ • g₂ ∂μ` whenever `g₁ = g₂` on `Ω`.

* `TestFunction.integrable_inner_subtype`: the pairing `⟪φ x, v x⟫` of a test vector field with a
  locally integrable field is integrable.

* `TestFunction.enorm_integral_inner_le_withDensity`: the pairing of a test field supported in `U`
  and bounded by `1` with `v` is at most the mass of `|v| m` on `U`.

* `TestFunction.integral_lineDeriv_eq_zero`: `∫ ∂_w φ dμ = 0` for an additive Haar measure `μ`.

* `IsOpen.eqOn_zero_of_integral_contDiff_smul_eq_zero`: a function continuous on an open set `U`
  whose integrals against smooth functions compactly supported in `U` vanish is zero on `U`.

* `TestFunction.ext_of_forall_integral_smul_eq`: a test function is determined by its integrals
  against smooth compactly supported functions.

* `TestFunction.tendsto_integral_bilin_of_tendsto_lintegral_enorm_sub`:
  `∫ P (φ ·) (g i ·) → ∫ P (φ ·) (g₀ ·)` when `g i → g₀` in `L¹` on a set containing
  `tsupport φ`.

* `TestFunction.tendsto_integral_bilin_clm_of_tendstoUniformlyOn`:
  `∫ P (φ ·) (A i · (u ·)) → ∫ P (φ ·) (B · (u ·))` when `A i` is eventually continuous and
  converges uniformly on `tsupport φ`, and `u` is locally integrable on `Ω`.

* `TestFunction.tendsto_integral_bilin_normed_convolution`:
  `∫ P (φ ·) (B ((ρ i ⋆ 1_W U) ·) (u ·)) → ∫ P (φ ·) (B (U ·) (u ·))` when `U ∈ Lᵖ(W)`,
  `u ∈ L^q(W)` and `p⁻¹ + q⁻¹ ≤ 1`.
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions BoundedContinuousFunction CompactlySupported RealInnerProductSpace ENNReal

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
      ((isClosed_tsupport _).preimage continuous_subtypeVal)
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

/-- The restriction of a test function to `Ω` is supported in the preimage of its support. -/
theorem tsupport_toCompactlySupportedContinuousMap_subset (φ : 𝓓^{n}(Ω, F)) :
    tsupport φ.toCompactlySupportedContinuousMap ⊆ ((↑) : Ω → E) ⁻¹' tsupport φ := by
  have h : ⇑φ.toCompactlySupportedContinuousMap = fun x : Ω => φ x :=
    funext (toCompactlySupportedContinuousMap_apply φ)
  rw [h]
  exact tsupport_comp_subset_preimage φ continuous_subtypeVal

/-- Extending the restriction of a test function on `Ω` by zero recovers the test function. -/
@[simp]
theorem coe_extendZero_toCompactlySupportedContinuousMap (φ : 𝓓^{n}(Ω, F)) :
    ⇑(φ.toCompactlySupportedContinuousMap.extendZero Ω.isOpenEmbedding') = ⇑φ := by
  ext x
  by_cases h : x ∈ Ω
  · exact CompactlySupportedContinuousMap.extendZero_apply _ _ (⟨x, h⟩ : Ω)
  · rw [CompactlySupportedContinuousMap.extendZero_apply_of_notMem_range _ _ (by simpa using h)]
    exact (φ.zero_on_compl h).symm

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

/-- The right-hand side `-(f + ∑ᵢⱼ Gᵢⱼ)` of a weak derivative equation, with `f` locally integrable
on `Ω` and each `φ Gᵢⱼ` integrable, tests against a real test function `φ` as follows:
`-∫ φ · -(f + ∑ᵢⱼ Gᵢⱼ) = ∫_Ω f φ + ∑ᵢⱼ ∫ φ Gᵢⱼ`. The two index types of the finite sum are
independent. -/
theorem neg_integral_smul_neg_add_eq [OpensMeasurableSpace E] {κ κ' : Type*} [Fintype κ]
    [Fintype κ'] {μ : Measure E} {f : E → ℝ} {G : κ → κ' → E → ℝ} (φ : 𝓓(Ω, ℝ))
    (hfloc : LocallyIntegrableOn f Ω μ)
    (hIG : ∀ i j, Integrable (fun x => (φ : E → ℝ) x • G i j x) μ) :
    -∫ x, (φ : E → ℝ) x • -(f x + ∑ i, ∑ j, G i j x) ∂μ =
      (∫ x in Ω, f x * φ x ∂μ) + ∑ i, ∑ j, ∫ x, (φ : E → ℝ) x • G i j x ∂μ := by
  simp only [smul_neg, integral_neg, neg_neg, smul_add, Finset.smul_sum]
  rw [integral_add (φ.integrable_smul hfloc)
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hIG i j),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hIG i j]
  congr 1
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [φ.zero_on_compl hx]]
    simp only [smul_eq_mul, mul_comm]
  · exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hIG i j

/-- Integrating against a test function on `Ω` only sees the integrand on `Ω`: if `g₁ = g₂` on `Ω`,
then `∫ φ • g₁ ∂μ = ∫ φ • g₂ ∂μ`. -/
theorem integral_smul_congr_of_eqOn (φ : 𝓓^{n}(Ω, ℝ)) {μ : Measure E} {g₁ g₂ : E → F}
    (h : Set.EqOn g₁ g₂ Ω) : ∫ x, (φ : E → ℝ) x • g₁ x ∂μ = ∫ x, (φ : E → ℝ) x • g₂ x ∂μ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ (Ω : Set E)
  · simp only [h hx]
  · simp [φ.zero_on_compl hx]

section InnerPairing

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [OpensMeasurableSpace E]

/-- The pairing of a test vector field with a locally integrable field is integrable. -/
theorem integrable_inner_subtype {m : Measure Ω} {v : Ω → G} (φ : 𝓓^{n}(Ω, G))
    (hv : LocallyIntegrable v m) : Integrable (fun x : Ω => ⟪φ x, v x⟫) m :=
  (φ.integrable_bilin_subtype (innerSL ℝ) hv).congr
    (ae_of_all _ fun _ => innerSL_apply_apply ℝ _ _)

omit [OpensMeasurableSpace E] in
/-- The pairing of a test vector field supported in `U` and bounded by `1` with a field `v` is
bounded by the mass of the measure `|v| m` on `U`. -/
theorem enorm_integral_inner_le_withDensity {U : Set E} (hU : MeasurableSet U)
    {φ : 𝓓^{n}(Ω, G)} (hφU : tsupport φ ⊆ U) (hφ : ∀ x, ‖φ x‖ ≤ 1) (m : Measure Ω) (v : Ω → G) :
    ‖∫ x : Ω, ⟪φ x, v x⟫ ∂m‖ₑ ≤
      m.withDensity (fun x => ‖v x‖ₑ) ((↑) ⁻¹' U) := by
  rw [withDensity_apply _ (hU.preimage measurable_subtypeVal),
    ← lintegral_indicator (hU.preimage measurable_subtypeVal)]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun x => ?_)
  by_cases hx : x ∈ ((↑) ⁻¹' U : Set Ω)
  · rw [Set.indicator_of_mem hx, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hφ x)))
  · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => hx (hφU hx')
    simp [hx, hzero]

end InnerPairing

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

variable [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The directional derivative of a test function has integral zero against an additive Haar
measure: `∫ ∂_w φ = 0`. -/
theorem integral_lineDeriv_eq_zero (φ : 𝓓(Ω, ℝ)) (w : E) :
    ∫ x, lineDeriv ℝ (φ : E → ℝ) x w ∂μ = 0 := by
  rcases φ.hasCompactSupport.eq_zero_or_finiteDimensional ℝ φ.continuous with h | hE
  · simp [h, lineDeriv]
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

section Determination

open Set
open scoped ContDiff

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] {μ : Measure E}
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- **Fundamental lemma of the calculus of variations for continuous functions.** A function
continuous on an open set `U` whose integrals against all smooth functions compactly supported in
`U` vanish is zero on `U`. -/
theorem _root_.IsOpen.eqOn_zero_of_integral_contDiff_smul_eq_zero {U : Set E} (hU : IsOpen U)
    {d : E → F} (hd : ContinuousOn d U)
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • d x ∂μ = 0) :
    EqOn d 0 U :=
  μ.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2
    (hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hd.locallyIntegrableOn hU.measurableSet) h))
    hU hd continuousOn_const

/-- A test function on `Ω` is determined by its integrals against smooth functions compactly
supported in `Ω`. -/
theorem ext_of_forall_integral_smul_eq {φ ψ : 𝓓^{n}(Ω, F)}
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ω →
      ∫ x, g x • φ x ∂μ = ∫ x, g x • ψ x ∂μ) :
    φ = ψ := by
  have hint (χ : 𝓓^{n}(Ω, F)) {g : E → ℝ} (hg : Continuous g) :
      Integrable (fun x ↦ g x • χ x) μ :=
    (hg.smul χ.continuous).integrable_of_hasCompactSupport χ.hasCompactSupport.smul_left
  have hEq := Ω.isOpen.eqOn_zero_of_integral_contDiff_smul_eq_zero (μ := μ) (d := ⇑φ - ⇑ψ)
    (φ.continuous.sub ψ.continuous).continuousOn fun g hg hgc hgΩ ↦ by
      simp_rw [Pi.sub_apply, smul_sub]
      rw [integral_sub (hint φ hg.continuous) (hint ψ hg.continuous), h g hg hgc hgΩ, sub_self]
  ext x
  by_cases hx : x ∈ (Ω : Set E)
  · simpa [sub_eq_zero] using hEq hx
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h),
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (ψ.tsupport_subset h)]

end Determination

section BilinConvergence

open Filter Set
open scoped Convolution Topology

/-- If `g i → g₀` in `L¹(s)` on a set `s` containing the topological support of `φ`, then the
bilinear pairings `∫ x, P (φ x) (g i x) ∂μ` converge to `∫ x, P (φ x) (g₀ x) ∂μ`. The
approximating pairings need only be eventually integrable, and the limiting pairing needs only to be
almost everywhere strongly measurable. -/
theorem tendsto_integral_bilin_of_tendsto_lintegral_enorm_sub
    {W₀ G' H' : Type*} [NormedAddCommGroup W₀] [NormedSpace ℝ W₀]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {μ : Measure E} {ι : Type*} {l : Filter ι} {s : Set E} (P : W₀ →L[ℝ] G' →L[ℝ] H')
    (φ : 𝓓^{n}(Ω, W₀)) (hφs : tsupport (φ : E → W₀) ⊆ s)
    {g : ι → E → G'} {g₀ : E → G'}
    (hg : ∀ᶠ i in l, Integrable (fun x => P ((φ : E → W₀) x) (g i x)) μ)
    (hg₀ : AEStronglyMeasurable (fun x => P ((φ : E → W₀) x) (g₀ x)) μ)
    (hlim : Tendsto (fun i => ∫⁻ x in s, ‖g i x - g₀ x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, P ((φ : E → W₀) x) (g i x) ∂μ) l
      (𝓝 (∫ x, P ((φ : E → W₀) x) (g₀ x) ∂μ)) := by
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hind : Tendsto (fun i => ∫⁻ x, ‖s.indicator (g i) x - s.indicator g₀ x‖ₑ ∂μ) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      fun i => (lintegral_mono fun x => by
        by_cases hx : x ∈ s <;> simp [hx]).trans (lintegral_indicator_le _ s)
  have hlimP := P.tendsto_lintegral_enorm_bilin_sub_of_norm_le (ae_of_all _ hM) hind
  refine tendsto_integral_of_L1 _ hg₀ hg (hlimP.congr fun i => lintegral_congr fun x => ?_)
  by_cases hxs : x ∈ s
  · simp [hxs]
  · simp [hxs, image_eq_zero_of_notMem_tsupport fun h => hxs (hφs h)]

/-- Pairing a `C^n` test function `φ` through `P` against `x ↦ A i x (u x)` converges to
`∫ x, P (φ x) (B x (u x)) ∂μ` when `A i → B` uniformly on `tsupport φ`, `A i` is eventually
continuous on `tsupport φ`, and `u` is locally integrable on `Ω`. -/
theorem tendsto_integral_bilin_clm_of_tendstoUniformlyOn [OpensMeasurableSpace E]
    {W₀ G' H' F' : Type*} [NormedAddCommGroup W₀] [NormedSpace ℝ W₀]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {μ : Measure E} {ι : Type*} {l : Filter ι}
    (P : W₀ →L[ℝ] G' →L[ℝ] H') (φ : 𝓓^{n}(Ω, W₀)) {u : E → F'} (hu : LocallyIntegrableOn u Ω μ)
    {A : ι → E → F' →L[ℝ] G'} {B : E → F' →L[ℝ] G'}
    (hA : ∀ᶠ i in l, ContinuousOn (A i) (tsupport (φ : E → W₀)))
    (hunif : TendstoUniformlyOn A B l (tsupport (φ : E → W₀))) :
    Tendsto (fun i => ∫ x, P ((φ : E → W₀) x) (A i x (u x)) ∂μ) l
      (𝓝 (∫ x, P ((φ : E → W₀) x) (B x (u x)) ∂μ)) := by
  rcases eq_or_neBot l with rfl | _
  · exact tendsto_bot
  set K := tsupport (φ : E → W₀)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have huK : IntegrableOn u K μ :=
    hu.integrableOn_compact_subset φ.tsupport_subset φ.hasCompactSupport
  have hint {C : E → F' →L[ℝ] G'} (hC : ContinuousOn C K) :
      Integrable (fun x => P ((φ : E → W₀) x) (C x (u x))) μ :=
    (integrableOn_iff_integrable_of_support_subset
      fun _ hx => subset_tsupport _ fun h0 => hx (by simp [h0])).1 <|
      memLp_one_iff_integrable.1 <| P.memLp_of_bilin 1 φ.memLp_top <|
        (ContinuousLinearMap.id ℝ (F' →L[ℝ] G')).memLp_of_bilin 1
          (hC.memLp_top_restrict_of_subset_isCompact φ.hasCompactSupport hKm subset_rfl)
          (memLp_one_iff_integrable.2 huK)
  have hsup : Tendsto (fun i => (⨆ y ∈ K, ‖A i y - B y‖ₑ) * ∫⁻ x in K, ‖u x‖ₑ ∂μ) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hunif.tendsto_iSup_enorm_sub (Or.inr huK.2.ne)
  refine φ.tendsto_integral_bilin_of_tendsto_lintegral_enorm_sub P subset_rfl
    (hA.mono fun _ => hint) (hint (hunif.continuousOn hA.frequently)).aestronglyMeasurable
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsup
      (fun _ => zero_le) fun i => ?_)
  rw [← lintegral_const_mul'' _ huK.aestronglyMeasurable.eNorm]
  refine setLIntegral_mono' hKm fun x hx => ?_
  rw [← sub_apply]
  have h1 : ‖(A i x - B x) (u x)‖ₑ ≤ ‖A i x - B x‖ₑ * ‖u x‖ₑ := by
    simpa only [← ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _)] using
      ENNReal.ofReal_le_ofReal ((A i x - B x).le_opNorm (u x))
  exact h1.trans (by gcongr; exact le_biSup (fun y => ‖A i y - B y‖ₑ) hx)

/-- Pairing a `C^n` test function supported in a null-measurable set `W` through `P` against
`x ↦ B (((ρ i).normed μ ⋆ 1_W U) x) (u x)` converges to `∫ x, P (φ x) (B (U x) (u x)) ∂μ` when
`U ∈ Lᵖ(W)`, `u ∈ L^q(W)` and `p⁻¹ + q⁻¹ ≤ 1` (allowing `p = ∞` or `q = ∞`). -/
theorem tendsto_integral_bilin_normed_convolution
    [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {W₀ H₀ H₁ F' G' : Type*} [NormedAddCommGroup W₀] [NormedSpace ℝ W₀]
    [NormedAddCommGroup H₀] [NormedSpace ℝ H₀] [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (P : W₀ →L[ℝ] H₀ →L[ℝ] H₁) (B : F' →L[ℝ] G' →L[ℝ] H₀)
    {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {W : Set E} (hW : NullMeasurableSet W μ) (φ : 𝓓^{n}(Ω, W₀))
    (hφW : tsupport (φ : E → W₀) ⊆ W) {U : E → F'} (hU : MemLp U p (μ.restrict W))
    {u : E → G'} (hu : MemLp u q (μ.restrict W))
    {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, P ((φ : E → W₀) x)
        (B (((ρ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] W.indicator U) x)
          (u x)) ∂μ)
      l (𝓝 (∫ x, P ((φ : E → W₀) x) (B (U x) (u x)) ∂μ)) := by
  let _ : Fact (1 ≤ p) := ⟨ENNReal.one_le_left_of_inv_add_inv_le_one hpq⟩
  have : p.HolderConjugate p.conjExponent := .conjExponent Fact.out
  have hp'q : p.conjExponent ≤ q := ENNReal.conjExponent_le_of_inv_add_inv_le_one hpq
  set K : Set E := tsupport (φ : E → W₀)
  have hKm : NullMeasurableSet K μ := (isClosed_tsupport _).measurableSet.nullMeasurableSet
  have : IsFiniteMeasure (μ.restrict K) :=
    isFiniteMeasure_restrict.2 φ.hasCompactSupport.measure_lt_top.ne
  have huK : MemLp u p.conjExponent (μ.restrict K) :=
    (hu.mono_measure (Measure.restrict_mono hφW le_rfl)).mono_exponent hp'q
  let C : W₀ →L[ℝ] G' →L[ℝ] F' →L[ℝ] H₁ :=
    ((ContinuousLinearMap.compL ℝ F' H₀ H₁).comp P).bilinearComp
      (ContinuousLinearMap.id ℝ W₀) B.flip
  have ha : MemLp (fun x => C ((φ : E → W₀) x) (K.indicator u x)) p.conjExponent μ :=
    C.memLp_of_bilin p.conjExponent φ.memLp_top ((memLp_indicator_iff_restrict hKm).2 huK)
  have hlim := (ContinuousLinearMap.id ℝ (F' →L[ℝ] H₁)).tendsto_integral_bilin_normed_convolution
    hρ ha ((memLp_indicator_iff_restrict hW).2 hU)
  have hpt (x : E) (y : F') :
      C ((φ : E → W₀) x) (K.indicator u x) y = P ((φ : E → W₀) x) (B y (u x)) := by
    by_cases hx : x ∈ K
    · simp [C, hx]
    · simp [C, image_eq_zero_of_notMem_tsupport hx]
  have hlim_rhs : ∫ x, P ((φ : E → W₀) x) (B (W.indicator U x) (u x)) ∂μ =
      ∫ x, P ((φ : E → W₀) x) (B (U x) (u x)) ∂μ :=
    integral_congr_ae (.of_forall fun x => by
      by_cases hx : x ∈ W
      · simp [hx]
      · simp [image_eq_zero_of_notMem_tsupport fun h => hx (hφW h)])
  simpa only [ContinuousLinearMap.id_apply, hpt, hlim_rhs] using hlim

end BilinConvergence

end TestFunction
