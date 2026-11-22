/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Basic
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Localization
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.Pseudodifferential.Composition.Sobolev
import TauCeti.Analysis.Pseudodifferential.FourierSchur
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Basic
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Microlocal Sobolev mapping of pseudodifferential operators

Let `a` be a symbol of order `m` on `ℝⁿ` with compact spatial support, and `Op(a) : H^t → H^{t - m}`
its quantization on Mathlib's Bessel-potential spaces (`TauCeti.Symbol.quantizeSobolev`). This
file proves that `Op(a)` loses `m` orders of Sobolev regularity *microlocally*: if the Fourier
transform `𝓕 u` of `u ∈ H^t` has `H^s` decay on an open cone `Γ` of frequencies, that is
`⟨ζ⟩ ^ s 𝓕 u` is square integrable on `Γ`, then `⟨ξ⟩ ^ (s - m) 𝓕 (Op(a) u)` is square integrable
on every cone `Γ'` whose conic neighbourhoods lie in `Γ`. Here `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`,
and an element `u ∈ H^t` is represented on the Fourier side by the `L²` function
`𝓕 u.toLp = ⟨ζ⟩ ^ t 𝓕 u` (`BesselPotentialSpace.toTemperedDistribution_fourier_toLp`).

For cut-off distributions this is the order shift of the `H^s` wave front set: if a complex
distribution `T` on an open set of `ℝⁿ` is microlocally `H^s` at `(x, ξ)`, then for every cutoff
`φ` supported near `x` and every scalar symbol `a` of order `m` with compact spatial support,
`Op(a) (φ T)` is `H^{s - m}` in an open cone around `ξ`
(`Distribution.IsMicrolocallySobolevAt.exists_nhds_cone_forall_memLp_quantizeSobolev`).

Removing the cutoff gives the order shift of the `H^s` wave front set itself: for a scalar symbol
`a` and `u ∈ H^t(ℝⁿ, ℂ)`, viewed as a distribution on an open set `Ω ⊆ ℝⁿ`,

`WF_{s - m}(Op(a) u) ⊆ WF_s(u)`

(`Symbol.HasCompactSpatialSupport.sobolevWaveFrontSet_toDistribution_quantizeSobolev_subset`),
and hence `singsupp_{s - m}(Op(a) u) ⊆ singsupp_s(u)`. Near a point `x` at which `u` is microlocally
`H^s` in the direction `ξ`, split `u = φ u + (1 - φ) u` with a cutoff `φ` equal to `1` near `x`.
The first part is the cut-off case. For the second, `ψ Op(a) ((1 - φ) u)` is the quantization of
a smoothing symbol applied to `u` whenever `φ = 1` near the support of `ψ`, by the locality of the
composition symbol (`TauCeti.Symbol.isSmoothing_sharp_sub_comp`), so `Op(a) ((1 - φ) u)` is smooth
near `x`.

## The argument

On Schwartz functions, `𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) 𝓕 u ζ dζ`, where `â(η, ξ)` is the
Fourier transform of the position slice `x ↦ a(x, ξ)`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`). The weighted kernel
`⟨ξ⟩ ^ (t - m) ⟨ζ⟩ ^ (-t) â(ξ - ζ, 2πζ)` is bounded by an integrable function of `ξ - ζ`
(`TauCeti.rpow_mul_norm_fourier_apply_le`), so by Schur's test it defines a bounded
operator on `L²` (`TauCeti.integralOperatorLp`). Both this operator and `Op(a)` are continuous on
`H^t`, and they agree on the dense subspace of Schwartz functions, so the convolution formula holds
almost everywhere for every `u ∈ H^t`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_toLp_quantizeSobolev_ae_eq`).

For `ξ ∈ Γ'` split the integral at `Γ`. For `ζ ∈ Γ`, Peetre's inequality bounds the integrand by
`k(ξ - ζ) ⟨ζ⟩ ^ s ‖𝓕 u ζ‖` with an integrable `k`, and `⟨ζ⟩ ^ s 𝓕 u` is square integrable on `Γ`.
For `ζ ∉ Γ` the frequencies are separated, `‖ξ - ζ‖ > c ‖ξ‖`, hence `‖ζ‖` is at most a multiple of
`1 + ‖ξ - ζ‖`, and the rapid decay of `â` in its first variable absorbs the missing weight
`⟨ζ⟩ ^ (s - t)`, leaving `k(ξ - ζ) ⟨ζ⟩ ^ t ‖𝓕 u ζ‖`, which is controlled by the `H^t` norm. Schur's
test (`TauCeti.memLp_lintegral_mul`) for the kernel `k(ξ - ζ)` applied to the sum of both pieces
gives the square integrability on `Γ'`
(`TauCeti.Symbol.HasCompactSpatialSupport.memLp_smul_fourier_toLp_quantizeSobolev`).

## Main results

* `TauCeti.Symbol.HasCompactSpatialSupport.fourier_toLp_quantizeSobolev_ae_eq`: the convolution
  formula for `𝓕 (Op(a) u)` on `H^t`.
* `TauCeti.Symbol.HasCompactSpatialSupport.memLp_smul_fourier_toLp_quantizeSobolev`: conic `H^s`
  regularity of `u` gives conic `H^{s - m}` regularity of `Op(a) u` on smaller cones.
* `Distribution.IsMicrolocallySobolevAt.exists_nhds_cone_forall_memLp_quantizeSobolev`: the order
  shift for cut-off distributions microlocally `H^s` at a point.
* `TauCeti.Symbol.HasCompactSpatialSupport.isMicrolocallySobolevAt_toDistribution_quantizeSobolev`:
  if `u ∈ H^t` is microlocally `H^s` at `(x, ξ)`, then `Op(a) u` is microlocally `H^{s - m}` there.
* `Symbol.HasCompactSpatialSupport.sobolevWaveFrontSet_toDistribution_quantizeSobolev_subset`:
  `WF_{s - m}(Op(a) u) ⊆ WF_s(u)`.
* `Symbol.HasCompactSpatialSupport.sobolevSingularSupport_toDistribution_quantizeSobolev_subset`:
  `singsupp_{s - m}(Op(a) u) ⊆ singsupp_s(u)`.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and its behaviour under pseudodifferential operators).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13
  (Sobolev continuity) and §18.1 (microlocality of pseudodifferential operators).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform TemperedDistribution Metric Function
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {a : Symbol n V W m}

/-! ### The convolution formula on `H^t` -/

/-- The weighted Fourier-side kernel `⟨ξ⟩ ^ (t - m) ⟨ζ⟩ ^ (-t) â(ξ - ζ, 2πζ)` of `Op(a)`, acting on
the `L²` representative `⟨ζ⟩ ^ t 𝓕 u` of `u ∈ H^t`. -/
private def fourierKernel (a : Symbol n V W m) (t : ℝ) (ξ ζ : CoordinateSpace n) : V →L[ℂ] W :=
  (((1 + ‖ξ‖ ^ 2) ^ ((t - m) / 2) * (1 + ‖ζ‖ ^ 2) ^ (-t / 2) : ℝ) : ℂ) •
    𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ)

omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.continuous_uncurry_fourierKernel
    (ha : a.HasCompactSpatialSupport) (t : ℝ) : Continuous (uncurry (a.fourierKernel t)) := by
  have hf : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦ (p.1 - p.2, (2 * π) • p.2) :=
    (continuous_fst.sub continuous_snd).prodMk (continuous_snd.const_smul (2 * π))
  have hslice := ha.continuous_fourier_slice.comp hf
  rw [uncurry_def]
  have hw (r : ℝ) : Continuous fun ξ : CoordinateSpace n ↦ (1 + ‖ξ‖ ^ 2) ^ (r / 2) :=
    (contDiff_one_add_norm_sq_rpow (n := 0) _).continuous
  exact (Complex.continuous_ofReal.comp (((hw (t - m)).comp continuous_fst).mul
    ((hw (-t)).comp continuous_snd))).smul hslice

omit [CompleteSpace V] [CompleteSpace W] in
/-- The pointwise kernel bounds behind the convolution formula and conic regularity: for an
integrable `k = B (1 + ‖·‖) ^ (-r)`, `⟨ξ⟩ ^ (s - m) ‖â(ξ - ζ, 2πζ) v‖` is at most
`k(ξ - ζ) ⟨ζ⟩ ^ s ‖v‖`, and at most `k(ξ - ζ) ⟨ζ⟩ ^ t ‖v‖` when `ζ` is separated from `ξ` by
`c ‖ξ‖ < ‖ξ - ζ‖`. -/
private theorem HasCompactSpatialSupport.exists_rpow_mul_norm_fourier_apply_le
    (ha : a.HasCompactSpatialSupport) (s t : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ B r : ℝ, 0 ≤ B ∧ (n : ℝ) < r ∧ ∀ (ξ ζ : CoordinateSpace n) (v : V),
      (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) v‖ ≤
        B * (1 + ‖ξ - ζ‖) ^ (-r) * ((1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖v‖) ∧
      (c * ‖ξ‖ < ‖ξ - ζ‖ →
        (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) v‖ ≤
          B * (1 + ‖ξ - ζ‖) ^ (-r) * ((1 + ‖ζ‖ ^ 2) ^ (t / 2) * ‖v‖)) := by
  set N : ℕ := ⌈|s - m| + |s - t|⌉₊ + n + 1
  obtain ⟨C₀, hC₀, hdecay⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le N
  set D := (c⁻¹ + 1) ^ |s - t|
  have hD : 1 ≤ D := Real.one_le_rpow (by linarith [inv_pos.2 hc]) (abs_nonneg _)
  set B₀ := 2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m|
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨B₀ * D, N - |s - m| - |s - t|, by positivity, ?_, fun ξ ζ v ↦ ?_⟩
  · have := Nat.le_ceil (|s - m| + |s - t|)
    push_cast [N]
    linarith
  set d := 1 + ‖ξ - ζ‖
  have hpt : (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) *
      ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) v‖ ≤
        B₀ * d ^ (-((N : ℝ) - |s - m|)) * ((1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖v‖) :=
    rpow_mul_norm_fourier_apply_le hdecay ξ ζ v
  have hd : 1 ≤ d := le_add_of_nonneg_right (norm_nonneg _)
  -- The decay exponent `N - |s - m|` exceeds `r` by `|s - t|`.
  have hsplit :
      d ^ (-((N : ℝ) - |s - m|)) * d ^ |s - t| = d ^ (-((N : ℝ) - |s - m| - |s - t|)) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  have hle : d ^ (-((N : ℝ) - |s - m|)) ≤ d ^ (-((N : ℝ) - |s - m| - |s - t|)) :=
    Real.rpow_le_rpow_of_exponent_le hd (by linarith [abs_nonneg (s - t)])
  refine ⟨hpt.trans ?_, fun hξζ ↦ hpt.trans ?_⟩
  · gcongr
    exact le_mul_of_one_le_right hB₀ hD
  · -- Away from `ξ`, the weight `⟨ζ⟩ ^ (s - t)` is absorbed by the decay in `ξ - ζ`.
    have hw := one_add_norm_sq_rpow_le_of_mul_norm_le_norm_sub hc hξζ.le (s - t)
    have hst :
        (1 + ‖ζ‖ ^ 2) ^ (s / 2) = (1 + ‖ζ‖ ^ 2) ^ ((s - t) / 2) * (1 + ‖ζ‖ ^ 2) ^ (t / 2) := by
      rw [← one_add_norm_sq_rpow_add, sub_add_cancel]
    calc B₀ * d ^ (-((N : ℝ) - |s - m|)) * ((1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖v‖)
        ≤ B₀ * d ^ (-((N : ℝ) - |s - m|)) *
            ((D * d ^ |s - t| * (1 + ‖ζ‖ ^ 2) ^ (t / 2)) * ‖v‖) := by
          rw [hst]
          gcongr
      _ = B₀ * D * (d ^ (-((N : ℝ) - |s - m|)) * d ^ |s - t|) *
            ((1 + ‖ζ‖ ^ 2) ^ (t / 2) * ‖v‖) := by ring
      _ = _ := by rw [hsplit]

omit [CompleteSpace V] [CompleteSpace W] in
/-- The weighted kernel is bounded by `B k(ξ - ζ)` for an integrable `k = (1 + ‖·‖) ^ (-r)`. -/
private theorem HasCompactSpatialSupport.exists_norm_fourierKernel_le
    (ha : a.HasCompactSpatialSupport) (t : ℝ) :
    ∃ B r : ℝ, 0 ≤ B ∧ (n : ℝ) < r ∧ ∀ ξ ζ : CoordinateSpace n,
      ‖a.fourierKernel t ξ ζ‖ ≤ B * (1 + ‖ξ - ζ‖) ^ (-r) := by
  obtain ⟨B, r, hB, hr, hpt⟩ := ha.exists_rpow_mul_norm_fourier_apply_le t t one_pos
  refine ⟨B, r, hB, hr, fun ξ ζ ↦ ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_⟩
  rw [fourierKernel, smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc _ = (1 + ‖ζ‖ ^ 2) ^ (-t / 2) * ((1 + ‖ξ‖ ^ 2) ^ ((t - m) / 2) *
          ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) v‖) := by ring
    _ ≤ (1 + ‖ζ‖ ^ 2) ^ (-t / 2) * (B * (1 + ‖ξ - ζ‖) ^ (-r) * ((1 + ‖ζ‖ ^ 2) ^ (t / 2) * ‖v‖)) :=
        mul_le_mul_of_nonneg_left (hpt ξ ζ v).1 (by positivity)
    _ = B * (1 + ‖ξ - ζ‖) ^ (-r) * ‖v‖ := by
        linear_combination (B * (1 + ‖ξ - ζ‖) ^ (-r) * ‖v‖) * one_add_norm_sq_rpow_neg_mul_rpow ζ t

/-- The row and column integrals of the kernel `B (1 + ‖ξ - ζ‖) ^ (-r)`, `B ≥ 0`, `r > n`, all
equal `∫ B (1 + ‖η‖) ^ (-r) dη`. -/
private theorem lintegral_ofReal_mul_one_add_norm_sub_rpow {B r : ℝ} (hB : 0 ≤ B)
    (hr : (n : ℝ) < r) :
    (∀ ξ : CoordinateSpace n, ∫⁻ ζ, ENNReal.ofReal (B * (1 + ‖ξ - ζ‖) ^ (-r)) =
        ENNReal.ofReal (∫ η : CoordinateSpace n, B * (1 + ‖η‖) ^ (-r))) ∧
      ∀ ζ : CoordinateSpace n, ∫⁻ ξ, ENNReal.ofReal (B * (1 + ‖ξ - ζ‖) ^ (-r)) =
        ENNReal.ofReal (∫ η : CoordinateSpace n, B * (1 + ‖η‖) ^ (-r)) := by
  have hk : Integrable fun η : CoordinateSpace n ↦ B * (1 + ‖η‖) ^ (-r) :=
    (integrable_one_add_norm (by rwa [finrank_euclideanSpace_fin])).const_mul B
  have hk0 : 0 ≤ᵐ[volume] fun η : CoordinateSpace n ↦ B * (1 + ‖η‖) ^ (-r) :=
    .of_forall fun _ ↦ mul_nonneg hB (by positivity)
  exact ⟨lintegral_ofReal_sub_left_eq_ofReal_integral hk hk0,
    lintegral_ofReal_sub_right_eq_ofReal_integral hk hk0⟩

omit [CompleteSpace V] [CompleteSpace W] in
/-- The row and column integrals of the weighted kernel are bounded. -/
private theorem HasCompactSpatialSupport.exists_lintegral_enorm_fourierKernel_le
    (ha : a.HasCompactSpatialSupport) (t : ℝ) :
    ∃ A : ℝ≥0, (∀ ξ, ∫⁻ ζ, ‖a.fourierKernel t ξ ζ‖ₑ ≤ A) ∧
      ∀ ζ, ∫⁻ ξ, ‖a.fourierKernel t ξ ζ‖ₑ ≤ A := by
  obtain ⟨B, r, hB, hr, hK⟩ := ha.exists_norm_fourierKernel_le t
  obtain ⟨hrow, hcol⟩ := lintegral_ofReal_mul_one_add_norm_sub_rpow hB hr
  have hle (ξ ζ : CoordinateSpace n) :
      ‖a.fourierKernel t ξ ζ‖ₑ ≤ ENNReal.ofReal (B * (1 + ‖ξ - ζ‖) ^ (-r)) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hK ξ ζ)
  exact ⟨_, fun ξ ↦ (lintegral_mono (hle ξ)).trans (hrow ξ).le,
    fun ζ ↦ (lintegral_mono (hle · ζ)).trans (hcol ζ).le⟩

/-- The convolution formula for a Schwartz function `v`: the integral operator of the weighted
kernel sends `⟨ζ⟩ ^ t 𝓕 v` to `⟨ξ⟩ ^ (t - m) 𝓕 (Op(a) v)`. -/
private theorem HasCompactSpatialSupport.fourier_toLp_quantizeSobolev_toBesselPotentialSpaceCLM
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (v : 𝓢(CoordinateSpace n, V)) {A : ℝ≥0}
    (hrow : ∀ᵐ ξ, ∫⁻ ζ, ‖a.fourierKernel t ξ ζ‖ₑ ≤ A)
    (hcol : ∀ᵐ ζ, ∫⁻ ξ, ‖a.fourierKernel t ξ ζ‖ₑ ≤ A)
    (hK : AEStronglyMeasurable (uncurry (a.fourierKernel t)) (volume.prod volume)) :
    𝓕 (a.quantizeSobolev ha t (SchwartzMap.toBesselPotentialSpaceCLM t 2 v)).toLp =
      integralOperatorLp (a.fourierKernel t) 2 hK hrow hcol
        (𝓕 (SchwartzMap.toBesselPotentialSpaceCLM t 2 v).toLp) := by
  have hw (r : ℝ) :
      (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  set w := (ha.hasCompactSupport_quantizeSchwartzValue v).toSchwartzMap
    (a.contDiff_quantizeSchwartzValue v)
  rw [ha.quantizeSobolev_toBesselPotentialSpaceCLM,
    SchwartzMap.fourier_toLp_toBesselPotentialSpaceCLM,
    SchwartzMap.fourier_toLp_toBesselPotentialSpaceCLM]
  refine Lp.ext ?_
  filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM W
      (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ ((t - m) / 2) : ℝ) : ℂ)) (𝓕 w)) 2,
    coeFn_integralOperatorLp (hA := hrow) (hB := hcol) ((SchwartzMap.smulLeftCLM V
      (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) (𝓕 v)).toLp 2)]
    with ξ h₁ h₂
  have hwq : ⇑w = quantizeSchwartzValue a.coefficient v :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [h₁, h₂, SchwartzMap.smulLeftCLM_apply_apply (hw _), SchwartzMap.fourier_coe, hwq,
    ha.fourier_quantizeSchwartzValue,
    ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM V
    (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) (𝓕 v)) 2] with ζ hζ
  rw [hζ, SchwartzMap.smulLeftCLM_apply_apply (hw _), fourierKernel, smul_apply, map_smul,
    smul_smul, ← Complex.ofReal_mul, mul_assoc, one_add_norm_sq_rpow_neg_mul_rpow, mul_one]

/-- **The convolution formula on `H^t`.** For a symbol `a` of order `m` with compact spatial
support and `u ∈ H^t`, the Fourier transform of `Op(a) u` is, almost everywhere,
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) 𝓕 u ζ dζ`, where `â(η, ξ)` is the Fourier transform of the position
slice `x ↦ a(x, ξ)` at `η`. Both sides are written through the `L²` representatives
`𝓕 u.toLp = ⟨ζ⟩ ^ t 𝓕 u` of `u ∈ H^t` and `⟨ξ⟩ ^ (t - m) 𝓕 (Op(a) u)` of `Op(a) u ∈ H^{t - m}`. -/
theorem HasCompactSpatialSupport.fourier_toLp_quantizeSobolev_ae_eq
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (u : H^{t}(CoordinateSpace n, V)) :
    ⇑(𝓕 (a.quantizeSobolev ha t u).toLp : Lp W 2 _)
      =ᵐ[volume] fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((t - m) / 2) : ℝ) : ℂ) •
        ∫ ζ, 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ)
          ((((1 + ‖ζ‖ ^ 2) ^ (-t / 2) : ℝ) : ℂ) •
            (𝓕 u.toLp : Lp V 2 _) ζ) := by
  obtain ⟨A, hrow, hcol⟩ := ha.exists_lintegral_enorm_fourierKernel_le t
  have hK : AEStronglyMeasurable (uncurry (a.fourierKernel t)) (volume.prod volume) :=
    (ha.continuous_uncurry_fourierKernel t).aestronglyMeasurable
  set T := integralOperatorLp (a.fourierKernel t) 2 hK (A := A) (B := A) (.of_forall hrow)
    (.of_forall hcol)
  set L₂ :=
    (Lp.fourierTransformₗᵢ (CoordinateSpace n) V).toContinuousLinearEquiv.toContinuousLinearMap
  set M₂ :=
    (Lp.fourierTransformₗᵢ (CoordinateSpace n) W).toContinuousLinearEquiv.toContinuousLinearMap
  -- Both sides as continuous linear maps of `u ∈ H^t`; they agree on Schwartz functions.
  have key : M₂ ∘L (BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) W (t - m) 2
        ).toContinuousLinearEquiv.toContinuousLinearMap ∘L a.quantizeSobolev ha t =
      T ∘L L₂ ∘L (BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V t 2
        ).toContinuousLinearEquiv.toContinuousLinearMap := by
    refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun v ↦ ?_
    have hv := ha.fourier_toLp_quantizeSobolev_toBesselPotentialSpaceCLM t v
      (.of_forall hrow) (.of_forall hcol) hK
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply, L₂, M₂]
    exact hv
  have hu : 𝓕 (a.quantizeSobolev ha t u).toLp = T (𝓕 u.toLp) := by
    have h := congrArg (fun F ↦ F u) key
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply, L₂,
      M₂] at h
    exact h
  rw [hu]
  filter_upwards [coeFn_integralOperatorLp (hA := .of_forall hrow) (hB := .of_forall hcol)
    (𝓕 u.toLp)] with ξ hξ
  rw [hξ, ← integral_smul]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  simp only [fourierKernel, smul_apply, map_smul, smul_smul, Complex.ofReal_mul]

/-! ### Conic regularity -/

omit [CompleteSpace V] [CompleteSpace W] in
/-- The pointwise bound of the integrand of the convolution formula on `Γ'`: it is at most
`k(ξ - ζ)` times `⟨ζ⟩ ^ (s - t) ‖G ζ‖` for `ζ ∈ Γ`, and times `‖G ζ‖` for `ζ ∉ Γ`. -/
private theorem enorm_fourier_slice_apply_le {s t B r c : ℝ} (hB : 0 ≤ B)
    (hpt : ∀ (ξ ζ : CoordinateSpace n) (v : V),
      (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) v‖ ≤
        B * (1 + ‖ξ - ζ‖) ^ (-r) * ((1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖v‖) ∧
      (c * ‖ξ‖ < ‖ξ - ζ‖ →
        (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) v‖ ≤
          B * (1 + ‖ξ - ζ‖) ^ (-r) * ((1 + ‖ζ‖ ^ 2) ^ (t / 2) * ‖v‖)))
    {Γ Γ' : Set (CoordinateSpace n)} (hΓΓ' : ∀ ξ ∈ Γ', closedBall ξ (c * ‖ξ‖) ⊆ Γ)
    {ξ : CoordinateSpace n} (hξ : ξ ∈ Γ') (G : CoordinateSpace n → V) (ζ : CoordinateSpace n) :
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2)) *
      ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ)
        ((((1 + ‖ζ‖ ^ 2) ^ (-t / 2) : ℝ) : ℂ) • G ζ)‖ₑ ≤
      ENNReal.ofReal (B * (1 + ‖ξ - ζ‖) ^ (-r)) *
        (Γ.indicator (fun ζ ↦ ‖(((1 + ‖ζ‖ ^ 2) ^ ((s - t) / 2) : ℝ) : ℂ) • G ζ‖ₑ) ζ + ‖G ζ‖ₑ) := by
  set v := (((1 + ‖ζ‖ ^ 2) ^ (-t / 2) : ℝ) : ℂ) • G ζ
  have hnorm (r' : ℝ) : (1 + ‖ζ‖ ^ 2) ^ (r' / 2) * ‖v‖ =
      ‖(((1 + ‖ζ‖ ^ 2) ^ ((r' - t) / 2) : ℝ) : ℂ) • G ζ‖ := by
    rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← mul_assoc,
      ← one_add_norm_sq_rpow_add, ← sub_eq_add_neg]
  have hk : 0 ≤ B * (1 + ‖ξ - ζ‖) ^ (-r) := mul_nonneg hB (by positivity)
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  by_cases hζ : ζ ∈ Γ
  · rw [Set.indicator_of_mem hζ]
    refine (ENNReal.ofReal_le_ofReal ((hpt ξ ζ v).1.trans_eq (by rw [hnorm]))).trans ?_
    rw [ENNReal.ofReal_mul hk, ofReal_norm]
    gcongr
    exact le_self_add
  · have hsep : c * ‖ξ‖ < ‖ξ - ζ‖ := by
      have h : ζ ∉ closedBall ξ (c * ‖ξ‖) := fun h ↦ hζ (hΓΓ' ξ hξ h)
      rwa [mem_closedBall, not_le, dist_eq_norm, norm_sub_rev] at h
    refine (ENNReal.ofReal_le_ofReal (((hpt ξ ζ v).2 hsep).trans_eq
      (by rw [hnorm, sub_self, zero_div, Real.rpow_zero, Complex.ofReal_one, one_smul]))).trans ?_
    rw [ENNReal.ofReal_mul hk, ofReal_norm]
    gcongr
    exact le_add_self

/-- Convolution with the integrable kernel `B (1 + ‖·‖) ^ (-r)`, `r > n`, preserves finiteness of
the `L²` norm, by Schur's test. -/
private theorem eLpNorm_lintegral_ofReal_mul_lt_top {B r : ℝ} (hB : 0 ≤ B) (hr : (n : ℝ) < r)
    {g : CoordinateSpace n → ℝ≥0∞} (hg : eLpNorm g 2 volume < ⊤) :
    eLpNorm (fun ξ ↦ ∫⁻ ζ, ENNReal.ofReal (B * (1 + ‖ξ - ζ‖) ^ (-r)) * g ζ) 2 volume < ⊤ := by
  obtain ⟨hrow, hcol⟩ := lintegral_ofReal_mul_one_add_norm_sub_rpow hB hr
  have hk : AEMeasurable (uncurry fun ξ ζ : CoordinateSpace n ↦
      ENNReal.ofReal (B * (1 + ‖ξ - ζ‖) ^ (-r))) (volume.prod volume) := by
    fun_prop
  exact (memLp_lintegral_mul hk (memLp_iff.2 hg) one_le_two
    (.of_forall fun ξ ↦ (hrow ξ).le) (.of_forall fun ζ ↦ (hcol ζ).le)).eLpNorm_lt_top

/-- **Microlocal Sobolev mapping.** Let `a` be a symbol of order `m` with compact spatial support
and `u ∈ H^t`. If `⟨ζ⟩ ^ s 𝓕 u` is square integrable on a measurable set of frequencies `Γ`, and
`Γ'` is a measurable set such that for some `c > 0` the closed ball of radius `c ‖ξ‖` about every
`ξ ∈ Γ'` lies in `Γ`, then `⟨ξ⟩ ^ (s - m) 𝓕 (Op(a) u)` is square integrable on `Γ'`. Both are
expressed through the `L²` representatives `𝓕 u.toLp = ⟨ζ⟩ ^ t 𝓕 u` and
`𝓕 (Op(a) u).toLp = ⟨ξ⟩ ^ (t - m) 𝓕 (Op(a) u)`, so the weights are `⟨·⟩ ^ (s - t)` on both
sides. Each point of an open cone `Γ` lies in an open cone `Γ'` of this kind
(`IsOpen.exists_cone_closedBall_subset`). -/
theorem HasCompactSpatialSupport.memLp_smul_fourier_toLp_quantizeSobolev
    (ha : a.HasCompactSpatialSupport) {s t : ℝ} {u : H^{t}(CoordinateSpace n, V)}
    {Γ Γ' : Set (CoordinateSpace n)} (hΓ : MeasurableSet Γ) (hΓ' : MeasurableSet Γ') {c : ℝ}
    (hc : 0 < c) (hΓΓ' : ∀ ξ ∈ Γ', closedBall ξ (c * ‖ξ‖) ⊆ Γ)
    (hu : MemLp (fun ζ ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - t) / 2) : ℝ) : ℂ) •
      (𝓕 u.toLp : Lp V 2 _) ζ) 2 (volume.restrict Γ)) :
    MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2) : ℝ) : ℂ) •
      (𝓕 (a.quantizeSobolev ha t u).toLp : Lp W 2 _) ξ) 2
      (volume.restrict Γ') := by
  obtain ⟨B, r, hB, hr, hpt⟩ := ha.exists_rpow_mul_norm_fourier_apply_le s t hc
  set G : CoordinateSpace n → V := ⇑(𝓕 u.toLp : Lp V 2 _)
  -- The input: `⟨ζ⟩ ^ (s - t) 𝓕 u.toLp` on `Γ`, and `𝓕 u.toLp` everywhere.
  set g : CoordinateSpace n → ℝ≥0∞ := fun ζ ↦
    Γ.indicator (fun ζ ↦ ‖(((1 + ‖ζ‖ ^ 2) ^ ((s - t) / 2) : ℝ) : ℂ) • G ζ‖ₑ) ζ + ‖G ζ‖ₑ
  have hbound : ∀ ξ ∈ Γ', ∀ ζ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2)) *
      ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ)
        ((((1 + ‖ζ‖ ^ 2) ^ (-t / 2) : ℝ) : ℂ) • G ζ)‖ₑ ≤
          ENNReal.ofReal (B * (1 + ‖ξ - ζ‖) ^ (-r)) * g ζ :=
    fun ξ hξ ζ ↦ enorm_fourier_slice_apply_le hB hpt hΓΓ' hξ G ζ
  have hGm : AEStronglyMeasurable G := Lp.aestronglyMeasurable _
  have hwG : AEStronglyMeasurable fun ζ ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - t) / 2) : ℝ) : ℂ) • G ζ :=
    (contDiff_ofReal_one_add_norm_sq_rpow (n := 0) _).continuous.aestronglyMeasurable.smul hGm
  have hg : eLpNorm g 2 volume < ⊤ := by
    refine (eLpNorm_add_le one_le_two).trans_lt (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · rw [eLpNorm_indicator_eq_eLpNorm_restrict hΓ.nullMeasurableSet,
        eLpNorm_eNorm _ hwG.restrict]
      exact hu.eLpNorm_lt_top
    · rw [eLpNorm_eNorm _ hGm]
      exact Lp.eLpNorm_lt_top _
  -- On `Γ'`, the weighted Fourier transform of `Op(a) u` is dominated by `k ⋆ g`.
  have hfm : AEStronglyMeasurable (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2) : ℝ) : ℂ) •
      (𝓕 (a.quantizeSobolev ha t u).toLp : Lp W 2 _) ξ) :=
    (contDiff_ofReal_one_add_norm_sq_rpow (n := 0) _).continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)
  refine lt_of_le_of_lt ?_ (eLpNorm_lintegral_ofReal_mul_lt_top hB hr hg)
  refine (eLpNorm_mono_eNorm_ae hfm.restrict ?_).trans
    (eLpNorm_mono_measure _ Measure.restrict_le_self)
  filter_upwards [ae_restrict_of_ae (ha.fourier_toLp_quantizeSobolev_ae_eq t u),
    ae_restrict_mem hΓ'] with ξ hξ hξΓ'
  rw [hξ, eNorm_eq_self, smul_smul, ← Complex.ofReal_mul, ← one_add_norm_sq_rpow_add,
    sub_add_sub_cancel, eNorm_smul, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_right (eNorm_integral_le_lintegral_eNorm _) _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono (hbound ξ hξΓ')

end Symbol

end TauCeti

namespace Distribution

open TauCeti TopologicalSpace
open scoped Distributions Topology

variable {n : ℕ} {Ω : Opens (CoordinateSpace n)}

/-- **The order shift of the `H^s` wave front set for cut-off distributions.** If a complex
distribution `T` on an open set `Ω ⊆ ℝⁿ` is microlocally `H^s` at `(x, ξ)`, there are a
neighbourhood `U` of `x` and an open cone `Γ` around `ξ` such that for every test function `φ`
supported in `U` and every scalar symbol `a` of order `m` with compact spatial support,
`⟨η⟩ ^ (s - m) 𝓕 (Op(a) (φ T))` is square integrable on `Γ`. Here `φ T ∈ H^t`
(every cut-off distribution lies in some `H^t`, `Distribution.exists_memSobolev_cutoffTempered`),
and `𝓕 (Op(a) (φ T)).toLp = ⟨η⟩ ^ (t - m) 𝓕 (Op(a) (φ T))`, so the weight in the statement is
`⟨η⟩ ^ (s - t)`. Thus `Op(a)` loses at most `m` orders of Sobolev regularity in the cone
directions near `ξ`, at every point of its output. -/
theorem IsMicrolocallySobolevAt.exists_nhds_cone_forall_memLp_quantizeSobolev {s : ℝ}
    {T : 𝓓'(Ω, ℂ)} {x ξ : CoordinateSpace n} (h : T.IsMicrolocallySobolevAt s x ξ) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set (CoordinateSpace n), IsOpen Γ ∧ ξ ∈ Γ ∧
      (∀ r : ℝ, 0 < r → ∀ η ∈ Γ, r • η ∈ Γ) ∧
      ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → ∀ {t : ℝ} (hφ : MemSobolev t 2 (T.cutoffTempered φ))
        {m : ℝ} (a : Symbol n ℂ ℂ m) (ha : a.HasCompactSpatialSupport),
        MemLp (fun η ↦ (((1 + ‖η‖ ^ 2) ^ ((s - t) / 2) : ℝ) : ℂ) •
          (𝓕 (a.quantizeSobolev ha t hφ.toBesselPotentialSpace).toLp : Lp ℂ 2 _) η) 2
          (volume.restrict Γ) := by
  obtain ⟨U, hU, Γ, hΓo, hξΓ, hcone, hL⟩ := h.exists_nhds_cone
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓΓ'⟩ := hΓo.exists_cone_closedBall_subset hcone hξΓ
  -- The `L²` representative of `φ T ∈ H^t` is `⟨ζ⟩ ^ t` times the localized Fourier transform.
  exact ⟨U, hU, Γ', hΓ'o, hξ', hcone', fun φ hφU t hφ m a ha ↦
    ha.memLp_smul_fourier_toLp_quantizeSobolev hΓo.measurableSet hΓ'o.measurableSet hc hΓΓ'
      ((hL φ hφU).ae_eq (ae_restrict_of_ae (one_add_norm_sq_rpow_smul_localFourier_ae_eq hφ s)))⟩

end Distribution

namespace TauCeti

namespace Symbol

open Distribution TopologicalSpace Set Filter
open scoped Distributions Topology ContDiff

variable {n : ℕ} {m : ℝ} {Ω : Opens (CoordinateSpace n)} {a : Symbol n ℂ ℂ m}

/-! ### The order shift of the `H^s` wave front set -/

/-- **Pseudodifferential operators lose their order microlocally.** Let `a` be a scalar symbol of
order `m` with compact spatial support and `u ∈ H^t`. If `u`, as a distribution on an open set
`Ω ⊆ ℝⁿ`, is microlocally `H^s` at `(x, ξ)`, then `Op(a) u` is microlocally `H^{s - m}` at
`(x, ξ)`. No `H^s` regularity of `u` away from `x`, or in other directions, is needed;
`u ∈ H^t` for some `t` suffices. -/
theorem HasCompactSpatialSupport.isMicrolocallySobolevAt_toDistribution_quantizeSobolev
    (ha : a.HasCompactSpatialSupport) {s t : ℝ} {u : H^{t}(CoordinateSpace n, ℂ)}
    {x ξ : CoordinateSpace n}
    (hu : (toDistribution Ω u.toDistr).IsMicrolocallySobolevAt s x ξ) :
    (toDistribution Ω (a.quantizeSobolev ha t u).toDistr).IsMicrolocallySobolevAt (s - m) x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySobolevAt_iff.1 hu
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓo, hξΓ, hcone, hL⟩ := hu.exists_nhds_cone_forall_memLp_quantizeSobolev
  -- Cutoffs `ψ` with `ψ x = 1`, and `φ` equal to `1` near `tsupport ψ`, both supported in `U`.
  have hW : interior U ∩ Ω ∈ 𝓝 x := inter_mem (interior_mem_nhds.2 hU) (Ω.isOpen.mem_nhds hx)
  obtain ⟨ψ, hψW, hψx⟩ :=
    TestFunction.exists_tsupport_subset_apply_eq (n := ⊤) hW inter_subset_right (1 : ℂ)
  obtain ⟨φ, hφ1, hφW⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    ψ.hasCompactSupport (isOpen_interior.inter Ω.isOpen) hψW inter_subset_right
  -- `ψ Op(a) = Op(c)` for the symbol `c = ψ # a`, which vanishes outside `tsupport ψ`.
  set ψ' := TestFunction.toSchwartzMapCLM ℂ ψ
  have hψ' : (ψ' : CoordinateSpace n → ℂ) = ψ := TestFunction.coe_toSchwartzMapCLM ψ
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := ℂ) (hψ' ▸ ψ.hasCompactSupport)
  set c := (ofSpatial (fun y ↦ ψ' y • ContinuousLinearMap.id ℂ ℂ)
    ((ψ'.smooth ⊤).smul contDiff_const)).sharp a ha
  have hc := hF.sharp ha
  have hψc (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ)) :
      TemperedDistribution.smulLeftCLM ℂ (ψ : CoordinateSpace n → ℂ)
        (a.quantizeSobolev ha t v).toDistr = (c.quantizeSobolev hc t v).toDistr :=
    hψ' ▸ smulLeftCLM_toDistr_quantizeSobolev ha hF t v
  set v := BesselPotentialSpace.smulLeftCLM t (TestFunction.toSchwartzMapCLM ℂ φ) u
  -- `Op(a) (φ u)` is microlocally `H^{s - m}` at `(x, ξ)`: `ψ Op(a) (φ u) = Op(c) (φ u)`, and
  -- `Op(c)` loses `m` orders in the cone `Γ` on the input `φ u`.
  have hA : (toDistribution Ω (a.quantizeSobolev ha t v).toDistr).IsMicrolocallySobolevAt
      (s - m) x ξ := by
    have hTφ : (toDistribution Ω u.toDistr).cutoffTempered φ = v.toDistr := by simp [v]
    have hφS := hTφ ▸ v.memSobolev_toDistr
    have hφv : hφS.toBesselPotentialSpace = v := hφS.toBesselPotentialSpace_eq_of_toDistr_eq hTφ
    have hLc := hφv ▸ hL φ (hφW.trans (inter_subset_left.trans interior_subset)) hφS c hc
    have hAS : MemSobolev (t - (0 + m)) 2 (TemperedDistribution.smulLeftCLM ℂ
        (ψ : CoordinateSpace n → ℂ) (a.quantizeSobolev ha t v).toDistr) :=
      hψc t v ▸ BesselPotentialSpace.memSobolev_toDistr _
    have hAc : hAS.toBesselPotentialSpace = c.quantizeSobolev hc t v :=
      hAS.toBesselPotentialSpace_eq_of_toDistr_eq (hψc t v)
    refine TemperedDistribution.isMicrolocallySobolevAt_toDistribution_iff.2
      ⟨ψ, by simp [hψx], Γ, hΓo, hξΓ, hcone, _, hAS, ?_⟩
    rwa [hAc, show s - m - (t - (0 + m)) = s - t by ring]
  -- `Op(a) ((1 - φ) u)` is `H^{s - m}` near `x`, since `ψ Op(a) ((1 - φ) u)` is smooth.
  have hB : (toDistribution Ω ((a.quantizeSobolev ha t u).toDistr -
      (a.quantizeSobolev ha t v).toDistr)).IsMicrolocallySobolevAt (s - m) x ξ := by
    refine (TemperedDistribution.isLocallySobolevAt_toDistribution_iff.2
      ⟨ψ, by simp [hψx], ?_⟩).isMicrolocallySobolevAt ξ
    rw [map_sub, hψc, hψc]
    exact memSobolev_toDistr_quantizeSobolev_sub_quantizeSobolev_smulLeftCLM hc
      (fun y hy ↦ coefficient_ofSpatial_smul_id_sharp_eq_zero_of_notMem_tsupport ha (hψ' ▸ hy))
      (by simpa using φ.hasCompactSupport) (hφ1.mono fun y hy ↦ by simpa using hy) t
      (s - m) u
  convert hA.add hB using 1
  rw [← map_add, add_sub_cancel]

/-- **The order shift of the `H^s` wave front set.** A scalar pseudodifferential operator of order
`m` with compact spatial support shifts the `H^s` wave front set by at most `m` orders: for
`u ∈ H^t` and every real `s`, as distributions on an open set `Ω ⊆ ℝⁿ`,

`WF_{s - m}(Op(a) u) ⊆ WF_s(u)`. -/
theorem HasCompactSpatialSupport.sobolevWaveFrontSet_toDistribution_quantizeSobolev_subset
    (ha : a.HasCompactSpatialSupport) (s : ℝ) {t : ℝ} (u : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution Ω (a.quantizeSobolev ha t u).toDistr).sobolevWaveFrontSet (s - m) ⊆
      (toDistribution Ω u.toDistr).sobolevWaveFrontSet s := by
  rintro ⟨y, η⟩ hp
  rw [mem_sobolevWaveFrontSet_iff] at hp ⊢
  exact ⟨hp.1, hp.2.1, fun h ↦ hp.2.2 (ha.isMicrolocallySobolevAt_toDistribution_quantizeSobolev h)⟩

/-- **The order shift of the `H^s` singular support.** For a scalar symbol `a` of order `m` with
compact spatial support and `u ∈ H^t`, the operator `Op(a)` maps distributions that are `H^s`
near a point to distributions that are `H^{s - m}` near it:
`singsupp_{s - m}(Op(a) u) ⊆ singsupp_s(u)` on every open set `Ω ⊆ ℝⁿ`. -/
theorem HasCompactSpatialSupport.sobolevSingularSupport_toDistribution_quantizeSobolev_subset
    (ha : a.HasCompactSpatialSupport) (s : ℝ) {t : ℝ} (u : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution Ω (a.quantizeSobolev ha t u).toDistr).sobolevSingularSupport (s - m) ⊆
      (toDistribution Ω u.toDistr).sobolevSingularSupport s := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet]
  exact image_mono (ha.sobolevWaveFrontSet_toDistribution_quantizeSobolev_subset s u)

end Symbol

end TauCeti
