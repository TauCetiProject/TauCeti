/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Properly supported pseudodifferential operators by localization near the diagonal

The Schwartz kernel `K_a(x, y)` of the quantization `Op(a)` of a symbol `a` on `ℝⁿ` is smooth off
the diagonal (`TauCeti.Symbol.offDiagonalKernel`), but it is not supported near the diagonal:
the support of `Op(a) u` is in general not contained in any bounded neighbourhood of the support
of `u`. Cutting the kernel off near the diagonal repairs this, at the cost of a smoothing error.

Fix a smooth function `χ` on `ℝⁿ` equal to `1` near `0`, typically with compact support. The
*removed kernel* `TauCeti.Symbol.smoothingKernel a χ` is

`R(x, y) = (1 - χ(x - y)) K_a(x, y)`.

It vanishes near the diagonal, so it is a smooth function on all of `ℝⁿ × ℝⁿ`, and it decays
faster than any power of `‖x - y‖`, locally uniformly in `x`. Its operator
`TauCeti.Symbol.smoothingRemainder a χ u (x) = ∫ R(x, y) u(y) dy` is therefore smoothing: it sends
compactly supported Schwartz functions to smooth functions. The *localized quantization*

`TauCeti.Symbol.properQuantizeValue a χ u = Op(a) u - ∫ R(·, y) u(y) dy`

has, off the diagonal, the kernel `χ(x - y) K_a(x, y)`, which vanishes unless `x - y` lies in
the support of `χ`. Hence it is properly supported: it sends a compactly supported Schwartz
function `u` to a smooth function supported in `supp u + supp χ`, and it differs from `Op(a)` by
the smoothing operator above.

## Main definitions

* `TauCeti.Symbol.smoothingKernel a χ`: the kernel `(1 - χ(x - y)) K_a(x, y)` removed by the
  cutoff.
* `TauCeti.Symbol.smoothingRemainder a χ`: its operator `u ↦ ∫ R(·, y) u(y) dy`.
* `TauCeti.Symbol.properQuantizeValue a χ`: the localized quantization `Op(a) - R`.

## Main results

* `TauCeti.Symbol.contDiff_smoothingKernel`: the removed kernel is smooth on `ℝⁿ × ℝⁿ`, and as
  regular as `χ` in general.
* `TauCeti.Symbol.exists_norm_smoothingKernel_le`: it decays like `(1 + ‖x - y‖)^(-2N)` for every
  `N` with `m - 2N < -n`, uniformly for `x` in a compact set.
* `TauCeti.Symbol.contDiff_smoothingRemainder`: the removed operator sends compactly supported
  Schwartz functions to smooth functions.
* `TauCeti.Symbol.properQuantizeValue_eq_integral_offDiagonalKernel`: **near-diagonal kernel**,
  away from the support of `u` the localized quantization is `∫ χ(x - y) K_a(x, y) u(y) dy`.
* `TauCeti.Symbol.support_properQuantizeValue_subset`,
  `TauCeti.Symbol.hasCompactSupport_properQuantizeValue`: **proper support**, the localized
  quantization of `u` is supported in `tsupport u + tsupport χ`, a compact set when `χ` has
  compact support.
* `TauCeti.Symbol.contDiff_properQuantizeValue`: the localized quantization of a compactly
  supported Schwartz function is smooth.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
-/

public section

open scoped SchwartzMap ContDiff Pointwise Topology
open MeasureTheory Function Filter

noncomputable section

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

namespace Symbol

variable {n : ℕ} {m : ℝ} {χ : CoordinateSpace n → ℝ}

/-! ### The removed kernel -/

/-- The part `(1 - χ(x - y)) K_a(x, y)` of the kernel of `Op(a)` that a near-diagonal cutoff `χ`
removes, where `K_a` is the off-diagonal kernel `TauCeti.Symbol.offDiagonalKernel`. When `χ` is
smooth and equal to `1` near `0` it is a smooth kernel (`TauCeti.Symbol.contDiff_smoothingKernel`)
decaying rapidly away from the diagonal (`TauCeti.Symbol.exists_norm_smoothingKernel_le`). -/
def smoothingKernel (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ) (x y : CoordinateSpace n) :
    V →L[ℂ] W :=
  (1 - χ (x - y)) • offDiagonalKernel a x y

theorem smoothingKernel_def (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (x y : CoordinateSpace n) :
    smoothingKernel a χ x y = (1 - χ (x - y)) • offDiagonalKernel a x y :=
  (rfl)

/-- Where the cutoff equals `1`, nothing of the kernel is removed. -/
theorem smoothingKernel_eq_zero (a : Symbol n V W m) {x y : CoordinateSpace n}
    (h : χ (x - y) = 1) : smoothingKernel a χ x y = 0 := by
  simp [smoothingKernel, h]

/-- Where the cutoff vanishes, the whole kernel is removed. -/
theorem smoothingKernel_eq_offDiagonalKernel (a : Symbol n V W m) {x y : CoordinateSpace n}
    (h : χ (x - y) = 0) : smoothingKernel a χ x y = offDiagonalKernel a x y := by
  simp [smoothingKernel, h]

/-- **Smoothness of the removed kernel.** If `χ` is of class `C^k` and equal to `1` near `0`, the
kernel `(1 - χ(x - y)) K_a(x, y)` is of class `C^k` on all of `ℝⁿ × ℝⁿ`: it vanishes near the
diagonal, and off the diagonal `K_a` is smooth (`TauCeti.Symbol.contDiffOn_offDiagonalKernel`).
In particular it is smooth when `χ` is. -/
theorem contDiff_smoothingKernel (a : Symbol n V W m) {k : ℕ∞} (hχ : ContDiff ℝ k χ)
    (hχ0 : χ =ᶠ[𝓝 0] 1) : ContDiff ℝ k (uncurry (smoothingKernel a χ)) := by
  refine contDiff_iff_contDiffAt.2 fun p ↦ ?_
  by_cases hp : p.1 = p.2
  · have hc : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2 := by fun_prop
    have hlim : Tendsto (fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2) (𝓝 p)
        (𝓝 0) := by
      simpa [hp] using hc.tendsto p
    refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    filter_upwards [hlim.eventually hχ0] with q hq
    exact smoothingKernel_eq_zero a hq
  · have ho : IsOpen {q : CoordinateSpace n × CoordinateSpace n | q.1 ≠ q.2} :=
      isOpen_ne_fun continuous_fst continuous_snd
    exact (contDiff_const.sub (hχ.comp (contDiff_fst.sub contDiff_snd))).contDiffAt.smul
      (((contDiffOn_offDiagonalKernel a).of_le (by exact_mod_cast le_top)).contDiffAt
        (ho.mem_nhds hp))

/-- If `χ` is continuous and equal to `1` near `0`, then for a fixed output position `x` the
removed kernel `y ↦ R(x, y)` is continuous. -/
theorem continuous_smoothingKernel_right (a : Symbol n V W m) (hχ : Continuous χ)
    (hχ0 : χ =ᶠ[𝓝 0] 1) (x : CoordinateSpace n) : Continuous (smoothingKernel a χ x) :=
  (contDiff_smoothingKernel a (k := 0) (contDiff_zero.2 hχ) hχ0).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- **Decay of the removed kernel.** If `χ` is continuous, compactly supported and equal to `1`
near `0`, then for every compact set `K` of positions and every `N` with `m - 2N < -n`,
`‖R(x, y)‖ ≤ C (1 + ‖x - y‖)^(-2N)` for `x ∈ K` and all `y`. -/
theorem exists_norm_smoothingKernel_le (a : Symbol n V W m) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχ0 : χ =ᶠ[𝓝 0] 1) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) {N : ℕ} (hN : m - 2 * N < -n) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ y, ‖smoothingKernel a χ x y‖ ≤ C / (1 + ‖x - y‖) ^ (2 * N) := by
  obtain ⟨r, hr, hχr⟩ := Metric.eventually_nhds_iff.1 hχ0
  obtain ⟨C₀, hC₀⟩ := exists_norm_offDiagonalKernel_le a hK hN
  obtain ⟨B, hB⟩ := hχ.bounded_above_of_compact_support hχc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨(1 + B) * |C₀| * ((1 + r) / r) ^ (2 * N), by positivity, fun x hx y ↦ ?_⟩
  rcases lt_or_ge ‖x - y‖ r with hxy | hxy
  · rw [smoothingKernel_eq_zero a (hχr (by simpa using hxy)), norm_zero]
    positivity
  set t := ‖x - y‖
  have ht : 0 < t := hr.trans_le hxy
  -- away from the diagonal, `1 + t ≤ ((1 + r) / r) t`
  have hq : (1 + t) ^ (2 * N) ≤ ((1 + r) / r) ^ (2 * N) * t ^ (2 * N) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    nlinarith
  have hχB : ‖1 - χ (x - y)‖ ≤ 1 + B := (norm_sub_le _ _).trans (by simpa using hB (x - y))
  have hK₀ : ‖offDiagonalKernel a x y‖ ≤ |C₀| / t ^ (2 * N) :=
    (hC₀ x hx y).trans (by gcongr; exact le_abs_self _)
  calc ‖smoothingKernel a χ x y‖ = ‖1 - χ (x - y)‖ * ‖offDiagonalKernel a x y‖ := by
        rw [smoothingKernel, norm_smul]
    _ ≤ (1 + B) * (|C₀| / t ^ (2 * N)) := by gcongr
    _ ≤ (1 + B) * (|C₀| * ((1 + r) / r) ^ (2 * N) / (1 + t) ^ (2 * N)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity), mul_assoc]
        exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
    _ = (1 + B) * |C₀| * ((1 + r) / r) ^ (2 * N) / (1 + t) ^ (2 * N) := by ring

/-- Against a Schwartz function, the removed kernel is integrable in the input variable. -/
theorem integrable_smoothingKernel_apply (a : Symbol n V W m) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχ0 : χ =ᶠ[𝓝 0] 1) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) : Integrable fun y ↦ smoothingKernel a χ x y (u y) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((m + n) / 2)
  obtain ⟨C, hC0, hC⟩ := exists_norm_smoothingKernel_le a hχ hχc hχ0
    isCompact_singleton (N := N) (by linarith)
  refine (u.integrable.norm.const_mul C).mono'
    ((continuous_smoothingKernel_right a hχ hχ0 x).clm_apply u.continuous).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact (hC x rfl y).trans (div_le_self hC0 (one_le_pow₀ (by simp)))

/-! ### The removed operator -/

/-- The smoothing operator `u ↦ ∫ R(·, y) u(y) dy` with the removed kernel
`R = TauCeti.Symbol.smoothingKernel a χ`, evaluated at `x`. -/
def smoothingRemainder (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) : W :=
  ∫ y, smoothingKernel a χ x y (u y)

theorem smoothingRemainder_def (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    smoothingRemainder a χ u x = ∫ y, smoothingKernel a χ x y (u y) :=
  (rfl)

/-- The removed operator is additive in the input. -/
theorem smoothingRemainder_add (a : Symbol n V W m) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχ0 : χ =ᶠ[𝓝 0] 1) (u v : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    smoothingRemainder a χ (u + v) x = smoothingRemainder a χ u x + smoothingRemainder a χ v x := by
  simp only [smoothingRemainder, add_apply, map_add]
  exact integral_add (integrable_smoothingKernel_apply a hχ hχc hχ0 u x)
    (integrable_smoothingKernel_apply a hχ hχc hχ0 v x)

/-- The removed operator is homogeneous in the input. -/
@[simp]
theorem smoothingRemainder_smul (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ) (c : ℂ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    smoothingRemainder a χ (c • u) x = c • smoothingRemainder a χ u x := by
  simp only [smoothingRemainder, smul_apply, map_smul]
  exact integral_smul c _

/-- **The removed operator is smoothing.** If `χ` is of class `C^k` and equal to `1` near `0`, the
removed operator sends a compactly supported Schwartz function to a `C^k` function; to a smooth
function when `χ` is smooth. -/
theorem contDiff_smoothingRemainder (a : Symbol n V W m) {k : ℕ∞} (hχ : ContDiff ℝ k χ)
    (hχ0 : χ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    ContDiff ℝ k (smoothingRemainder a χ u) := by
  have hu' : ContDiff ℝ k fun p : CoordinateSpace n × CoordinateSpace n ↦ u p.2 :=
    (u.smooth k).comp contDiff_snd
  -- Restrict the kernel to real scalars, since smoothness is over the real base.
  have hK := (ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).contDiff.comp
    (contDiff_smoothingKernel a hχ hχ0)
  have hf : ContDiff ℝ k fun p : CoordinateSpace n × CoordinateSpace n ↦
      uncurry (smoothingKernel a χ) p (u p.2) := by
    simpa only [Function.comp_apply, ContinuousLinearMap.coe_restrict_scalarsL',
      ContinuousLinearMap.coe_restrictScalars'] using hK.clm_apply hu'
  have h := ContDiff.parametric_integral (f := fun x y ↦ smoothingKernel a χ x y (u y))
    (μ := volume) hu.isCompact subset_rfl hu.isCompact.measure_lt_top.ne hf
  -- the integrand vanishes outside `tsupport u`
  have heq : smoothingRemainder a χ u =
      fun x ↦ ∫ y in tsupport u, smoothingKernel a χ x y (u y) :=
    funext fun x ↦ (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      simp [image_eq_zero_of_notMem_tsupport hy]).symm
  rw [heq]
  exact h

/-! ### The localized quantization -/

/-- The quantization of `a` localized near the diagonal by the cutoff `χ`:
`Op(a) u (x) - ∫ R(x, y) u(y) dy`, with the removed kernel
`R(x, y) = (1 - χ(x - y)) K_a(x, y)`. Off the diagonal its kernel is `χ(x - y) K_a(x, y)`
(`TauCeti.Symbol.properQuantizeValue_eq_integral_offDiagonalKernel`), so when `χ` has compact
support it is properly supported (`TauCeti.Symbol.hasCompactSupport_properQuantizeValue`). -/
def properQuantizeValue (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) : W :=
  quantizeSchwartzValue a.coefficient u x - smoothingRemainder a χ u x

theorem properQuantizeValue_def (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    properQuantizeValue a χ u x =
      quantizeSchwartzValue a.coefficient u x - smoothingRemainder a χ u x :=
  (rfl)

/-- The quantization is the localized quantization plus the removed smoothing operator. -/
@[simp]
theorem properQuantizeValue_add_smoothingRemainder (a : Symbol n V W m)
    (χ : CoordinateSpace n → ℝ) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    properQuantizeValue a χ u x + smoothingRemainder a χ u x =
      quantizeSchwartzValue a.coefficient u x :=
  sub_add_cancel _ _

/-- The localized quantization is additive in the input. -/
theorem properQuantizeValue_add (a : Symbol n V W m) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχ0 : χ =ᶠ[𝓝 0] 1) (u v : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    properQuantizeValue a χ (u + v) x =
      properQuantizeValue a χ u x + properQuantizeValue a χ v x := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  rw [properQuantizeValue, properQuantizeValue, properQuantizeValue,
    quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable hC,
    smoothingRemainder_add a hχ hχc hχ0]
  abel

/-- The localized quantization is homogeneous in the input. -/
@[simp]
theorem properQuantizeValue_smul (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ) (c : ℂ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    properQuantizeValue a χ (c • u) x = c • properQuantizeValue a χ u x := by
  simp [properQuantizeValue, smul_sub]

/-- **Smoothness.** If `χ` is of class `C^k` and equal to `1` near `0`, the localized quantization
of a compactly supported Schwartz function is of class `C^k`; smooth when `χ` is smooth. -/
theorem contDiff_properQuantizeValue (a : Symbol n V W m) {k : ℕ∞} (hχ : ContDiff ℝ k χ)
    (hχ0 : χ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    ContDiff ℝ k (properQuantizeValue a χ u) :=
  ((a.contDiff_quantizeSchwartzValue u).of_le (by exact_mod_cast le_top)).sub
    (contDiff_smoothingRemainder a hχ hχ0 hu)

/-- **The near-diagonal kernel.** If `χ` is continuous and equal to `1` near `0`, and the compactly
supported Schwartz function `u` vanishes near `x`, then the localized quantization at `x` is
`∫ χ(x - y) K_a(x, y) u(y) dy`. -/
theorem properQuantizeValue_eq_integral_offDiagonalKernel [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hχ : Continuous χ) (hχ0 : χ =ᶠ[𝓝 0] 1)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) {x : CoordinateSpace n}
    (hx : x ∉ tsupport u) :
    properQuantizeValue a χ u x = ∫ y, χ (x - y) • offDiagonalKernel a x y (u y) := by
  have hsupp {f : CoordinateSpace n → V →L[ℂ] W} : support (fun y ↦ f y (u y)) ⊆ tsupport u :=
    fun y hy ↦ subset_tsupport u fun h ↦ hy (by simp [h])
  have hK : Integrable fun y ↦ offDiagonalKernel a x y (u y) := by
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
    refine ContinuousOn.integrableOn_compact hu.isCompact ?_
    exact ((continuousOn_offDiagonalKernel_right a x).mono fun y hy (hxy : y = x) ↦
      hx (hxy ▸ hy)).clm_apply u.continuous.continuousOn
  have hR : Integrable fun y ↦ smoothingKernel a χ x y (u y) :=
    ((continuous_smoothingKernel_right a hχ hχ0 x).clm_apply
      u.continuous).integrable_of_hasCompactSupport (hu.mono' hsupp)
  rw [properQuantizeValue, quantizeSchwartzValue_eq_integral_offDiagonalKernel a hu hx,
    smoothingRemainder, ← integral_sub hK hR]
  congr 1 with y
  rw [smoothingKernel, smul_apply, sub_smul, one_smul, sub_sub_cancel]

/-- **Vanishing away from the support.** If `χ` equals `1` near `0` and
`x ∉ tsupport u + tsupport χ` for a compactly supported Schwartz function `u`, the localized
quantization vanishes at `x`. -/
theorem properQuantizeValue_eq_zero [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    (hχ0 : χ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u)
    {x : CoordinateSpace n} (hx : x ∉ tsupport u + tsupport χ) :
    properQuantizeValue a χ u x = 0 := by
  have h0 : (0 : CoordinateSpace n) ∈ tsupport χ :=
    subset_tsupport χ (by simp [hχ0.eq_of_nhds])
  have hxu : x ∉ tsupport u := fun h ↦ hx ⟨x, h, 0, h0, add_zero x⟩
  rw [properQuantizeValue, quantizeSchwartzValue_eq_integral_offDiagonalKernel a hu hxu,
    smoothingRemainder, sub_eq_zero]
  congr 1 with y
  by_cases hy : y ∈ tsupport u
  · have hχxy : x - y ∉ tsupport χ := fun h ↦ hx ⟨y, hy, x - y, h, add_sub_cancel y x⟩
    rw [smoothingKernel_eq_offDiagonalKernel a (image_eq_zero_of_notMem_tsupport hχxy)]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Proper support.** If `χ` equals `1` near `0`, the localized quantization of a compactly
supported Schwartz function `u` is supported in `tsupport u + tsupport χ`. -/
theorem support_properQuantizeValue_subset [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hχ0 : χ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport u) :
    support (properQuantizeValue a χ u) ⊆ tsupport u + tsupport χ := fun _ hx ↦
  by_contra fun h ↦ hx (properQuantizeValue_eq_zero a hχ0 hu h)

/-- **Proper support, closed form.** If `χ` has compact support and equals `1` near `0`, the
closed support of the localized quantization of a compactly supported Schwartz function `u` lies
in the compact set `tsupport u + tsupport χ`. -/
theorem tsupport_properQuantizeValue_subset [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hχc : HasCompactSupport χ) (hχ0 : χ =ᶠ[𝓝 0] 1)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    tsupport (properQuantizeValue a χ u) ⊆ tsupport u + tsupport χ :=
  closure_minimal (support_properQuantizeValue_subset a hχ0 hu)
    (hu.isCompact.add hχc.isCompact).isClosed

/-- **Compact support is preserved.** If `χ` has compact support and equals `1` near `0`, the
localized quantization of a compactly supported Schwartz function has compact support. -/
theorem hasCompactSupport_properQuantizeValue [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hχc : HasCompactSupport χ) (hχ0 : χ =ᶠ[𝓝 0] 1)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    HasCompactSupport (properQuantizeValue a χ u) :=
  (hu.isCompact.add hχc.isCompact).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_properQuantizeValue_subset a hχc hχ0 hu)

end Symbol

end TauCeti
