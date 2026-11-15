/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Pointwise
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Cutoff Cauchy–Green representation and translation of the Cauchy transform

Multiplying a function `f : ℂ → F` holomorphic on an open set `U ⊆ ℂ` by a compactly supported
`C¹` cutoff `α : ℂ → ℂ` with `tsupport α ⊆ U` globalizes `α • f` to a compactly supported `C¹`
map on `ℂ` whose conjugate Wirtinger derivative is `(bar∂ α) • f` everywhere: on `U` the holomorphic
factor satisfies `bar∂ f = 0`, while outside `tsupport α` both sides vanish identically.

Applying the compact-support Cauchy–Pompeiu inversion formula
`HasCompactSupport.cauchyTransform_conjWirtingerDeriv` to `α • f` recovers `α • f` as the Cauchy
transform of `(bar∂ α) • f`. When `α` is constant on an open subset `V`, `bar∂ α` vanishes on `V` as
well as outside `tsupport α`, so the plane integral collapses to the compact transition band
`tsupport α \ V`. In particular, if `α = 1` on `V`, then for every `ξ ∈ V`,
`f ξ = π⁻¹ • ∫ ζ in tsupport α \ V, (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ)`. Because `ξ ∈ V`
is separated from `tsupport α \ V`, the integrand has no singularity on the integration domain and
can be discretized directly by Riemann sums to build finite-rank Runge operators.

This module also records translation commutation of `TauCeti.cauchyTransform` and the
`HasCompactSupport` specializations of supercritical `Lᵖ` integrability, additivity, continuity,
and off-support holomorphy from `TauCeti.Analysis.Complex.Pompeiu.Pointwise`.

## Main declarations

* `TauCeti.cauchyTransform_comp_sub_right` and `TauCeti.cauchyTransform_comp_add_right`:
  `cauchyTransform` commutes with translations of `ℂ`.
* `HasCompactSupport.integrable_sub_inv_smul_of_memLp` and `TauCeti.cauchyTransform_add_of_memLp`:
  pointwise integrability and additivity of `cauchyTransform` on compactly supported supercritical
  `Lᵖ` data (`q < 2`, including `p = ∞`).
* `HasCompactSupport.continuous_cauchyTransform_of_norm_le` and
  `HasCompactSupport.differentiableOn_cauchyTransform_compl_tsupport_of_memLp`: global continuity
  for bounded measurable compactly supported data and holomorphy off `tsupport`.
* `DifferentiableOn.contDiff_smul_of_tsupport_subset` and
  `DifferentiableOn.conjWirtingerDeriv_smul_of_tsupport_subset`: global `Cⁿ` regularity and the
  exact formula `bar∂ (α • f) = (bar∂ α) • f` for a cutoff of a holomorphic map.
* `DifferentiableOn.smul_eq_cauchyTransform_conjWirtingerDeriv_smul`,
  `DifferentiableOn.smul_eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_smul`,
  `DifferentiableOn.eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_smul`, and
  `DifferentiableOn.eq_pi_inv_mul_setIntegral_conjWirtingerDeriv_mul`: the cutoff Cauchy–Green
  representation on `V` reduced to the compact support band `tsupport α \ V`.

## References

* A. Rainer, *Advanced Complex Analysis*, proof of Theorem 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorems
  1.2.1 and 1.3.1.
-/

public noncomputable section

open Complex Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

section CauchyTransform

/-- Translating the source by `-a` translates the Cauchy transform by `-a`. -/
theorem cauchyTransform_comp_sub_right (f : ℂ → F) (a w : ℂ) :
    cauchyTransform (fun z ↦ f (z - a)) w = cauchyTransform f (w - a) := by
  simp only [cauchyTransform_apply]
  congr 1
  have h := integral_sub_right_eq_self (μ := volume) (fun z : ℂ ↦ (w - a - z)⁻¹ • f z) a
  simpa only [sub_sub_sub_cancel_right] using h

/-- Translating the source by `+a` translates the Cauchy transform by `+a`. -/
theorem cauchyTransform_comp_add_right (f : ℂ → F) (a w : ℂ) :
    cauchyTransform (fun z ↦ f (z + a)) w = cauchyTransform f (w + a) := by
  simpa only [sub_neg_eq_add] using cauchyTransform_comp_sub_right f (-a) w

/-- Compactly supported supercritical `Lᵖ` data (`q < 2`, including `p = ∞`, `q = 1`) have an
absolutely convergent Cauchy integral at every point. -/
theorem _root_.HasCompactSupport.integrable_sub_inv_smul_of_memLp {p q : ℝ≥0∞}
    [p.HolderConjugate q] (hq : q < 2) {f : ℂ → F} (hfc : HasCompactSupport f)
    (hf : MemLp f p volume) (w : ℂ) :
    Integrable (fun z ↦ (w - z)⁻¹ • f z) volume := by
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  exact TauCeti.integrable_sub_inv_smul_of_memLp hq hf ((subset_tsupport f).trans hr) w

/-- The Cauchy transform is additive on compactly supported supercritical `Lᵖ` data (`q < 2`,
including bounded measurable compactly supported data at `p = ∞`, `q = 1`). -/
theorem cauchyTransform_add_of_memLp {p q : ℝ≥0∞} [p.HolderConjugate q] (hq : q < 2)
    {f g : ℂ → F} (hfc : HasCompactSupport f) (hf : MemLp f p volume)
    (hgc : HasCompactSupport g) (hg : MemLp g p volume) :
    cauchyTransform (f + g) = cauchyTransform f + cauchyTransform g := by
  funext w
  simp only [cauchyTransform_apply, Pi.add_apply, smul_add]
  rw [integral_add (hfc.integrable_sub_inv_smul_of_memLp hq hf w)
    (hgc.integrable_sub_inv_smul_of_memLp hq hg w), smul_add]

/-- The Cauchy transform of an essentially bounded measurable map with compact support is
continuous on `ℂ`. -/
theorem _root_.HasCompactSupport.continuous_cauchyTransform_of_norm_le {f : ℂ → F}
    (hfc : HasCompactSupport f) (hf : AEStronglyMeasurable f volume) {M : ℝ}
    (hM : ∀ᵐ z, ‖f z‖ ≤ M) :
    Continuous (cauchyTransform f) := by
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  exact TauCeti.continuous_cauchyTransform_of_norm_le hf ((subset_tsupport f).trans hr) hM

/-- The Cauchy transform of compactly supported `Lᵖ` data with `1 ≤ p` is holomorphic off
`tsupport f`. -/
theorem _root_.HasCompactSupport.differentiableOn_cauchyTransform_compl_tsupport_of_memLp
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℂ → F} (hfc : HasCompactSupport f) (hf : MemLp f p volume) :
    DifferentiableOn ℂ (cauchyTransform f) (tsupport f)ᶜ := by
  have : Fact (volume (tsupport f) < ⊤) := ⟨hfc.isCompact.measure_lt_top⟩
  have hint : Integrable f volume :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
      ((hf.restrict (tsupport f)).integrable hp)
  exact differentiableOn_cauchyTransform_compl_tsupport hint

end CauchyTransform

section CutoffPompeiu

/-- Multiplying a Banach-space-valued function holomorphic on an open set `U ⊆ ℂ` by a scalar `Cⁿ`
cutoff supported inside `U` produces a globally `Cⁿ` map on `ℂ`. -/
theorem _root_.DifferentiableOn.contDiff_smul_of_tsupport_subset [CompleteSpace F]
    {n : WithTop ℕ∞} {U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    {α : ℂ → ℂ} (hα : ContDiffOn ℝ n α U) (hαU : tsupport α ⊆ U) :
    ContDiff ℝ n (fun z ↦ α z • f z) :=
  (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).flip.contDiff_of_tsupport_subset_right
    ((hf.contDiffOn hU).restrict_scalars ℝ) hα hU hαU

/-- For `f : ℂ → F` holomorphic on an open set `U ⊆ ℂ` and `α : ℂ → ℂ` real-differentiable on `U`
with `tsupport α ⊆ U`, the global identity `bar∂ (α • f) = (bar∂ α) • f` holds at every point of
`ℂ`. -/
theorem _root_.DifferentiableOn.conjWirtingerDeriv_smul_of_tsupport_subset {U : Set ℂ}
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) {α : ℂ → ℂ}
    (hα : DifferentiableOn ℝ α U) (hαU : tsupport α ⊆ U) (w v : ℂ) :
    conjWirtingerDeriv (fun z ↦ α z • f z) w v = conjWirtingerDeriv α w v • f w := by
  by_cases hw : w ∈ U
  · have hfw : DifferentiableAt ℂ f w := (hf w hw).differentiableAt (hU.mem_nhds hw)
    have hαw : DifferentiableAt ℝ α w := (hα w hw).differentiableAt (hU.mem_nhds hw)
    rw [conjWirtingerDeriv_smul_apply hαw (hfw.restrictScalars ℝ) v,
      hfw.conjWirtingerDeriv_eq_zero, zero_apply, smul_zero, zero_add]
  · have hnot : w ∉ tsupport α := fun h ↦ hw (hαU h)
    have hzero : (fun z ↦ α z • f z) =ᶠ[𝓝 w] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with z hz
      simp [hz]
    rw [hzero.conjWirtingerDeriv_eq, conjWirtingerDeriv_of_notMem_tsupport hnot]
    simp

/-- **Global cutoff Cauchy–Green identity.** If `f : ℂ → F` is holomorphic on an open set `U ⊆ ℂ`
and `α : ℂ → ℂ` is `C¹` on `U` with compact support inside `U`, then `α • f` equals the Cauchy
transform of `ζ ↦ conjWirtingerDeriv α ζ 1 • f ζ` everywhere on `ℂ`. -/
theorem _root_.DifferentiableOn.smul_eq_cauchyTransform_conjWirtingerDeriv_smul [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) {α : ℂ → ℂ}
    (hα : ContDiffOn ℝ 1 α U) (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ U) (w : ℂ) :
    α w • f w = cauchyTransform (fun ζ ↦ conjWirtingerDeriv α ζ 1 • f ζ) w := by
  have hu_cpt : HasCompactSupport (fun z ↦ α z • f z) := hαc.smul_right
  have hu_diff : ContDiff ℝ 1 (fun z ↦ α z • f z) :=
    hf.contDiff_smul_of_tsupport_subset hU hα hαU
  have hderiv (ζ : ℂ) :
      conjWirtingerDeriv (fun z ↦ α z • f z) ζ 1 = conjWirtingerDeriv α ζ 1 • f ζ :=
    hf.conjWirtingerDeriv_smul_of_tsupport_subset hU (hα.differentiableOn one_ne_zero) hαU ζ 1
  simpa only [hderiv] using (hu_cpt.cauchyTransform_conjWirtingerDeriv hu_diff w).symm

/-- If in addition `α` is constant on an open set `V`, the Cauchy–Green integral for `α • f`
reduces to the compact transition band `tsupport α \ V`. -/
theorem _root_.DifferentiableOn.smul_eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_smul
    [CompleteSpace F] {U V : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hV : IsOpen V) {α : ℂ → ℂ} (hα : ContDiffOn ℝ 1 α U) (hαc : HasCompactSupport α)
    (hαU : tsupport α ⊆ U) {c : ℂ} (hαV : ∀ z ∈ V, α z = c) (w : ℂ) :
    α w • f w =
      (Real.pi : ℂ)⁻¹ •
        ∫ ζ in tsupport α \ V, (w - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ) := by
  rw [hf.smul_eq_cauchyTransform_conjWirtingerDeriv_smul hU hα hαc hαU w, cauchyTransform_apply]
  congr 1
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ ↦ ?_
  suffices conjWirtingerDeriv α ζ 1 = 0 by simp [this]
  by_cases hζts : ζ ∈ tsupport α
  · have hζV : ζ ∈ V := by_contra fun hnotV ↦ hζ ⟨hζts, hnotV⟩
    have hev : α =ᶠ[𝓝 ζ] fun _ ↦ c :=
      Filter.eventually_of_mem (hV.mem_nhds hζV) fun z hz ↦ hαV z hz
    rw [hev.conjWirtingerDeriv_eq, (differentiableAt_const c).conjWirtingerDeriv_eq_zero,
      zero_apply]
  · rw [conjWirtingerDeriv_of_notMem_tsupport hζts, zero_apply]

/-- **Cutoff Cauchy–Green representation on the interior plateau.** Let `f : ℂ → F` be holomorphic
on an open set `U ⊆ ℂ` with values in a complex Banach space `F`, and let `α : ℂ → ℂ` be a
compactly supported cutoff that is `C¹` on `U`, satisfies `tsupport α ⊆ U`, and equals `1` on an
open subset `V`. Then for every `ξ ∈ V`,
`f ξ = π⁻¹ • ∫ ζ in tsupport α \ V, (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ)`. -/
theorem _root_.DifferentiableOn.eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_smul
    [CompleteSpace F] {U V : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hV : IsOpen V) {α : ℂ → ℂ} (hα : ContDiffOn ℝ 1 α U) (hαc : HasCompactSupport α)
    (hαU : tsupport α ⊆ U) (hαV : ∀ z ∈ V, α z = 1) {ξ : ℂ} (hξ : ξ ∈ V) :
    f ξ =
      (Real.pi : ℂ)⁻¹ •
        ∫ ζ in tsupport α \ V, (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ) := by
  have h := hf.smul_eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_smul hU hV hα hαc hαU
    (c := 1) (fun z hz ↦ hαV z hz) ξ
  simpa only [hαV ξ hξ, one_smul] using h

/-- Scalar form of `DifferentiableOn.eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_smul` for
complex-valued holomorphic functions. -/
theorem _root_.DifferentiableOn.eq_pi_inv_mul_setIntegral_conjWirtingerDeriv_mul
    {U V : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hV : IsOpen V)
    {α : ℂ → ℂ} (hα : ContDiffOn ℝ 1 α U) (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ U)
    (hαV : ∀ z ∈ V, α z = 1) {ξ : ℂ} (hξ : ξ ∈ V) :
    f ξ =
      (Real.pi : ℂ)⁻¹ *
        ∫ ζ in tsupport α \ V, (ξ - ζ)⁻¹ * conjWirtingerDeriv α ζ 1 * f ζ := by
  simpa only [smul_eq_mul, mul_assoc] using
    hf.eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_smul hU hV hα hαc hαU hαV hξ

end CutoffPompeiu

end TauCeti
