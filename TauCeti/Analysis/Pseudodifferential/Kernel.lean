/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The kernel of the Kohn–Nirenberg quantization

The left quantization `Op(a) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) u(y) dy dξ` of a
coefficient `a : E × E → (V →L[ℂ] W)` is formally the integral operator with kernel

`K_a(x, y) = (2π)⁻ⁿ ∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) dξ = ∫ exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ) dζ`,

the inverse Fourier transform of the rescaled frequency slice `ζ ↦ a(x, 2πζ)`, evaluated at the
displacement `x - y`. For a general symbol of order `m` this integral does not converge and `K_a`
is a distribution. When the frequency slice `ξ ↦ a(x, ξ)` is integrable, which holds for a symbol
of order `m < -n` with `n = finrank ℝ E`, the integral converges absolutely and `K_a` is an honest
function. This file defines `TauCeti.quantizationKernel a x y` by the absolutely convergent
formula, and proves for such coefficients that it is the kernel of `TauCeti.quantizeSchwartzValue`.
For a coefficient whose frequency slice is not integrable the Bochner integral has the junk value
`0`; in particular the definition is not the kernel of the identity, which is the Dirac mass on
the diagonal.

## Main results

* `TauCeti.quantizationKernel_eq_fourierInv` and `TauCeti.quantizationKernel_eq_smul_integral`:
  the kernel is the inverse Fourier transform of the rescaled frequency slice, equivalently the
  angular-frequency integral `(2π)⁻ⁿ ∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) dξ`.
* `TauCeti.norm_quantizationKernel_le`: `‖K_a(x, y)‖ ≤ (2π)⁻ⁿ ∫ ‖a(x, ξ)‖ dξ`, uniformly in `y`.
* `TauCeti.continuous_quantizationKernel_right` and `TauCeti.continuous_quantizationKernel`:
  `y ↦ K_a(x, y)` is continuous when the frequency slice at `x` is integrable, and `K_a` is jointly
  continuous for a continuous coefficient with growth bounds `‖a(x, ξ)‖ ≤ C_K ⟨ξ⟩ ^ m`, `m < -n`,
  uniform for `x` in compact sets.
* `TauCeti.quantizeSchwartzValue_eq_integral_quantizationKernel`: **kernel representation**,
  `Op(a) u (x) = ∫ K_a(x, y) u(y) dy` for every Schwartz function `u`.
* `TauCeti.eq_quantizationKernel_of_forall`: **uniqueness**, a continuous kernel representing
  `u ↦ Op(a) u (x)` on Schwartz functions is `y ↦ K_a(x, y)`.
* `TauCeti.inner_smul_quantizationKernel`: multiplying the kernel by `⟪x - y, v⟫` corresponds to
  the frequency derivative `i ∂_{ξ, v}` of the coefficient, which lowers the order of a symbol by
  one. This is the first-order case `⟪x - y, v⟫ K_a = K_{-D_{ξ, v} a}`; iterating it gives
  `(x - y)^α K_a = K_{(-D_ξ)^α a}` when all the derivatives are integrable, the identity behind
  the smoothness and decay of pseudodifferential kernels off the diagonal.
* `TauCeti.Symbol.integrable_coefficient`, `TauCeti.Symbol.continuous_quantizationKernel` and
  `TauCeti.Symbol.quantizationKernel_frequencyDeriv`: for a symbol `a ∈ S^m_{1,0}` with `m < -n`
  the frequency slices are integrable, the kernel is continuous, and the kernel of `∂_{ξ_j} a` is
  `-i (x - y)_j K_a(x, y)`.
* `TauCeti.Symbol.quantizationKernel_mixedDeriv_replicate` and
  `TauCeti.Symbol.one_add_norm_div_pow_mul_norm_quantizationKernel_le`: iterating, the kernel of
  `∂_{ξ_j}^k a` is `(-i (x - y)_j)^k K_a(x, y)`, so the kernel decays off the diagonal at a rate
  controlled by the frequency integrals of the derivatives: if `∫ ‖a(x, ξ)‖ dξ ≤ A` and
  `∫ ‖∂_{ξ_j}^N a(x, ξ)‖ dξ ≤ A R^N` for every `j`, then
  `(1 + ‖x - y‖ / R)^N ‖K_a(x, y)‖ ≤ 2^N (1 + √n^N) (2π)⁻ⁿ A`.
* `TauCeti.Symbol.contDiff_quantizationKernel` and
  `TauCeti.Symbol.IsSmoothing.contDiff_quantizationKernel`: **regularity of the kernel**. For a
  symbol of order `m` with `m + k < -n` the kernel is `C^k` in `(x, y)`, since every derivative of
  `K_a` is the kernel of a symbol of one order higher, a position derivative of `a` or `a` times
  `i ⟪ξ, ·⟫`. The kernel of a smoothing symbol is therefore smooth.
* `TauCeti.Symbol.norm_sq_smul_quantizationKernel` and
  `TauCeti.Symbol.contDiffOn_quantizationKernel`: `‖x - y‖² K_a = K_{-Δ_ξ a}` for a symbol of order
  `m < -n`, where `Δ_ξ` is the frequency Laplacian (`TauCeti.Symbol.frequencyLaplacian`). Dividing
  by `‖x - y‖^(2N)` the kernel of the symbol `(-Δ_ξ)^N a` of order `m - 2N`, which is `C^k` for
  large `N`, shows that `K_a` is smooth off the diagonal.
* `TauCeti.Symbol.offDiagonalKernel` and
  `TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`: **the kernel off the
  diagonal** for a symbol of any order. The function
  `K(x, y) = ‖x - y‖^(-2N) K_{(-Δ_ξ)^N a}(x, y)`, with `N` so large that `(-Δ_ξ)^N a` has order
  below `-n`, represents the quantization away from the diagonal:
  `Op(a) u (x) = ∫ K(x, y) u(y) dy` for every compactly supported Schwartz function `u` vanishing
  near `x`. The proof moves the factor `‖x - y‖^(2N)` onto the input, where multiplying by
  `‖x - y‖²` before quantizing at `x` replaces `a` by `-Δ_ξ a`
  (`TauCeti.Symbol.quantizeSchwartzValue_smulLeftCLM_norm_sub_sq`). The kernel is smooth on
  `x ≠ y` (`TauCeti.Symbol.contDiffOn_offDiagonalKernel`), it is the only continuous kernel with
  this property (`TauCeti.Symbol.eqOn_offDiagonalKernel_of_forall`), and it agrees with `K_a` when
  `m < -n` (`TauCeti.Symbol.offDiagonalKernel_eq_quantizationKernel`). Pseudodifferential operators
  are thus given by smooth kernels away from the diagonal.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
open MeasureTheory Real FourierTransform Module

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The kernel of the left (Kohn–Nirenberg) quantization of a coefficient map `a(x, ξ)`:

`quantizationKernel a x y = ∫ exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ) dζ`.

It is the kernel of `quantizeSchwartzValue a` when `ξ ↦ a(x, ξ)` is integrable
(`quantizeSchwartzValue_eq_integral_quantizationKernel`); otherwise the integral has the junk
value `0`. See `quantizationKernel_eq_smul_integral` for the formula in the angular frequency. -/
def quantizationKernel (a : E × E → V →L[ℂ] W) (x y : E) : V →L[ℂ] W :=
  ∫ ζ, 𝐞 ⟪ζ, x - y⟫ • a (x, (2 * π) • ζ)

theorem quantizationKernel_def (a : E × E → V →L[ℂ] W) (x y : E) :
    quantizationKernel a x y = ∫ ζ, 𝐞 ⟪ζ, x - y⟫ • a (x, (2 * π) • ζ) :=
  (rfl)

/-- The kernel is the inverse Fourier transform of the rescaled frequency slice, evaluated at the
displacement `x - y`. -/
theorem quantizationKernel_eq_fourierInv (a : E × E → V →L[ℂ] W) (x y : E) :
    quantizationKernel a x y = 𝓕⁻ (fun ζ ↦ a (x, (2 * π) • ζ)) (x - y) := by
  rw [quantizationKernel_def, Real.fourierInv_eq]

/-- **Change of frequency.** With `n = finrank ℝ E`, the kernel is the angular-frequency integral
`(2π)⁻ⁿ ∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) dξ`. -/
theorem quantizationKernel_eq_smul_integral (a : E × E → V →L[ℂ] W) (x y : E) :
    quantizationKernel a x y = ((2 * π) ^ finrank ℝ E)⁻¹ •
      ∫ ξ, Complex.exp (⟪x - y, ξ⟫ * Complex.I) • a (x, ξ) := by
  have hpos : 0 < ((2 * π) ^ finrank ℝ E)⁻¹ := by positivity
  rw [← abs_of_pos hpos, ← Measure.integral_comp_smul, quantizationKernel_def]
  congr 1 with ζ
  rw [Circle.smul_def, Real.fourierChar_apply, inner_smul_right, real_inner_comm]

variable {a : E × E → V →L[ℂ] W} {x : E}

/-- The kernel integrand at `(x, y)` is integrable when the frequency slice `ξ ↦ a(x, ξ)` is. -/
theorem integrable_quantizationKernel_integrand (ha : Integrable (fun ξ ↦ a (x, ξ))) (y : E) :
    Integrable (fun ζ ↦ 𝐞 ⟪ζ, x - y⟫ • a (x, (2 * π) • ζ)) := by
  simpa only [inner_neg_right, neg_neg] using
    (Real.fourierIntegral_convergent_iff (-(x - y))).2 (ha.comp_smul two_pi_pos.ne')

/-- **Uniform bound.** `‖K_a(x, y)‖ ≤ (2π)⁻ⁿ ∫ ‖a(x, ξ)‖ dξ` for every `y`. -/
theorem norm_quantizationKernel_le (a : E × E → V →L[ℂ] W) (x y : E) :
    ‖quantizationKernel a x y‖ ≤ ((2 * π) ^ finrank ℝ E)⁻¹ * ∫ ξ, ‖a (x, ξ)‖ := by
  have hpos : 0 < ((2 * π) ^ finrank ℝ E)⁻¹ := by positivity
  rw [← abs_of_pos hpos, ← smul_eq_mul,
    ← Measure.integral_comp_smul (μ := volume) (f := fun ξ ↦ ‖a (x, ξ)‖)]
  exact (norm_integral_le_integral_norm _).trans_eq
    (by simp_rw [Circle.norm_smul (E := V →L[ℂ] W)])

/-- The kernel is linear in the coefficient: it vanishes for the zero coefficient. -/
@[simp]
theorem quantizationKernel_zero (x y : E) :
    quantizationKernel (0 : E × E → V →L[ℂ] W) x y = 0 := by
  simp [quantizationKernel_def, Circle.smul_def]

/-- The kernel is homogeneous in the coefficient. -/
@[simp]
theorem quantizationKernel_smul (c : ℂ) (a : E × E → V →L[ℂ] W) (x y : E) :
    quantizationKernel (c • a) x y = c • quantizationKernel a x y := by
  simp only [quantizationKernel_def, Pi.smul_apply, smul_comm (𝐞 _) c]
  exact integral_smul c _

/-- The kernel is additive in the coefficient at every position where both frequency slices are
integrable. -/
theorem quantizationKernel_add {b : E × E → V →L[ℂ] W} (ha : Integrable (fun ξ ↦ a (x, ξ)))
    (hb : Integrable (fun ξ ↦ b (x, ξ))) (y : E) :
    quantizationKernel (a + b) x y = quantizationKernel a x y + quantizationKernel b x y := by
  rw [quantizationKernel_def, quantizationKernel_def, quantizationKernel_def,
    ← integral_add (integrable_quantizationKernel_integrand ha y)
      (integrable_quantizationKernel_integrand hb y)]
  congr 1 with ζ
  simp only [Pi.add_apply, Circle.smul_def, smul_add]

/-- **Continuity in the second variable.** If the frequency slice `ξ ↦ a(x, ξ)` is integrable, then
`y ↦ K_a(x, y)` is continuous. -/
theorem continuous_quantizationKernel_right (ha : Integrable (fun ξ ↦ a (x, ξ))) :
    Continuous (quantizationKernel a x) := by
  rw [funext (quantizationKernel_eq_fourierInv a x)]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner.neg (ha.comp_smul two_pi_pos.ne')).comp (continuous_const.sub continuous_id)

/-- The weight `⟨2πζ⟩ ^ s` is integrable for `s < -n`, `n = finrank ℝ E`. -/
private theorem integrable_one_add_norm_two_pi_smul_sq_rpow {s : ℝ} (hs : s < -finrank ℝ E) :
    Integrable (fun ζ : E ↦ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (s / 2)) := by
  have h := (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure E))
    (r := -s) (by linarith)).comp_smul two_pi_pos.ne'
  simpa only [neg_neg] using h

/-- **Joint continuity.** For a continuous coefficient whose growth bound
`‖a(x, ξ)‖ ≤ C_K ⟨ξ⟩ ^ m` with `m < -n` is uniform for `x` in each compact set `K`, the kernel
`(x, y) ↦ K_a(x, y)` is continuous. -/
theorem continuous_quantizationKernel (ha : Continuous a) {m : ℝ} (hm : m < -finrank ℝ E)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    Continuous (Function.uncurry (quantizationKernel a)) := by
  have hweight := integrable_one_add_norm_two_pi_smul_sq_rpow (E := E) hm
  have hcont : Continuous fun q : (E × E) × E ↦
      𝐞 ⟪q.2, q.1.1 - q.1.2⟫ • a (q.1.1, (2 * π) • q.2) :=
    (Real.continuous_fourierChar.comp (continuous_snd.inner
      ((continuous_fst.comp continuous_fst).sub (continuous_snd.comp continuous_fst)))).smul
      (ha.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.const_smul _)))
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨C, hC⟩ := hC _ (isCompact_closedBall p₀.1 1)
  exact continuousAt_of_dominated
    (Filter.Eventually.of_forall fun p ↦
      (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.mem_of_superset (continuous_fst.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds p₀.1 one_pos)) fun p hp ↦ ae_of_all _ fun ζ ↦ by
        rw [Circle.norm_smul (E := V →L[ℂ] W)]
        exact hC p.1 hp _)
    (hweight.const_mul C)
    (ae_of_all _ fun ζ ↦ (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt)

/-- **Kernel representation.** If the frequency slice `ξ ↦ a(x, ξ)` is integrable, the
quantization of a Schwartz function is the integral operator with kernel `K_a`:
`Op(a) u (x) = ∫ K_a(x, y) u(y) dy`. -/
theorem quantizeSchwartzValue_eq_integral_quantizationKernel [CompleteSpace V] [CompleteSpace W]
    (ha : Integrable (fun ξ ↦ a (x, ξ))) (u : 𝓢(E, V)) :
    quantizeSchwartzValue a u x = ∫ y, quantizationKernel a x y (u y) := by
  -- Self-adjointness of the Fourier transform, `∫ M (𝓕 u) g = ∫ M u (𝓕 g)`, for the evaluation
  -- pairing `M` and `g ζ = 𝐞 ⟪ζ, x⟫ • a(x, 2πζ)`, whose Fourier transform at `y` is `K_a(x, y)`.
  have hg : Integrable (fun ζ : E ↦ 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ)) := by
    simpa only [sub_zero] using integrable_quantizationKernel_integrand ha 0
  -- The Fourier transform of a function is `VectorFourier.fourierIntegral 𝐞 volume (innerₗ E)` by
  -- definition, and `M = ContinuousLinearMap.apply ℂ W` evaluates `g ζ` at `𝓕 u ζ`.
  have h : ∫ ζ, (𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ)) (𝓕 (u : E → V) ζ) =
      ∫ y, VectorFourier.fourierIntegral 𝐞 volume (innerₗ E).flip
        (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ)) y (u y) :=
    VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.apply ℂ W)
      Real.continuous_fourierChar continuous_inner (u.integrable (μ := volume)) hg
  have hK (y : E) : VectorFourier.fourierIntegral 𝐞 volume (innerₗ E).flip
      (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ)) y = quantizationKernel a x y := by
    rw [VectorFourier.fourierIntegral, quantizationKernel_def]
    congr 1 with ζ
    rw [smul_smul, ← AddChar.map_add_eq_mul, LinearMap.flip_apply, innerₗ_apply_apply,
      real_inner_comm, inner_sub_right, neg_add_eq_sub]
  simp only [hK] at h
  rw [quantizeSchwartzValue_def, SchwartzMap.fourier_coe, ← h]
  simp only [Circle.smul_def, smul_apply]

/-- **Uniqueness of the kernel.** If the frequency slice `ξ ↦ a(x, ξ)` is integrable and a
continuous `K` represents `u ↦ Op(a) u (x)` on Schwartz functions, `Op(a) u (x) = ∫ K(y) u(y) dy`,
then `K` is the kernel `y ↦ K_a(x, y)`. -/
theorem eq_quantizationKernel_of_forall [CompleteSpace V] [CompleteSpace W] {K : E → V →L[ℂ] W}
    (hK : Continuous K) (ha : Integrable (fun ξ ↦ a (x, ξ)))
    (h : ∀ u : 𝓢(E, V), quantizeSchwartzValue a u x = ∫ y, K y (u y)) :
    K = quantizationKernel a x := by
  have hK₀ := continuous_quantizationKernel_right ha
  funext y
  ext v
  -- Test against `y ↦ g(y) v` for smooth compactly supported real `g`.
  have hae : ∀ᵐ y, K y v = quantizationKernel a x y v := by
    refine ae_eq_of_integral_contDiff_smul_eq (hK.clm_apply continuous_const).locallyIntegrable
      (hK₀.clm_apply continuous_const).locallyIntegrable fun g hg hgs ↦ ?_
    have hgc : ContDiff ℝ ∞ (fun y ↦ (g y : ℂ) • v) :=
      (Complex.ofRealCLM.contDiff.comp hg).smul contDiff_const
    have hgcs : HasCompactSupport (fun y ↦ (g y : ℂ) • v) :=
      (hgs.comp_left Complex.ofReal_zero).smul_right
    have hpt (L : E → V →L[ℂ] W) (y : E) : g y • L y v = L y ((hgcs.toSchwartzMap hgc) y) := by
      rw [HasCompactSupport.toSchwartzMap_toFun, map_smul, Complex.coe_smul]
    simp_rw [hpt K, hpt (quantizationKernel a x), ← h,
      quantizeSchwartzValue_eq_integral_quantizationKernel ha]
  exact congrFun ((hK.clm_apply continuous_const).ae_eq_iff_eq volume
    (hK₀.clm_apply continuous_const) |>.1 hae) y

/-- **Multiplication by the displacement.** If `ξ ↦ a(x, ξ)` has line derivative `a'(x, ξ)` in
the direction `v` and both are integrable, then `⟪x - y, v⟫ K_a(x, y) = i K_{a'}(x, y)`. In terms
of `D = -i ∂`, multiplying the kernel by `⟪x - y, v⟫` replaces the coefficient by
`-D_{ξ, v} a = i ∂_{ξ, v} a`, a symbol of one order lower. -/
theorem inner_smul_quantizationKernel {a' : E × E → V →L[ℂ] W} {v : E}
    (hda : ∀ ξ, HasLineDerivAt ℝ (fun ξ ↦ a (x, ξ)) (a' (x, ξ)) ξ v)
    (ha : Integrable (fun ξ ↦ a (x, ξ))) (ha' : Integrable (fun ξ ↦ a' (x, ξ))) (y : E) :
    (⟪x - y, v⟫ : ℂ) • quantizationKernel a x y = Complex.I • quantizationKernel a' x y := by
  -- Integrate by parts in `ζ` the product of `𝐞 ⟪ζ, z⟫`, whose line derivative is `c 𝐞 ⟪ζ, z⟫`,
  -- with `a(x, 2πζ)`, whose line derivative is `2π a'(x, 2πζ)`. This gives
  -- `2π K_{a'} = -c K_a`, and the claim follows by solving for `K_{a'}`.
  set z := x - y
  set c : ℂ := 2 * π * Complex.I * ⟪v, z⟫
  -- The character `ζ ↦ 𝐞 ⟪ζ, z⟫` has line derivative `c 𝐞 ⟪ζ, z⟫` along `v`: Mathlib's derivative
  -- of `ζ ↦ 𝐞 (-L ζ w)` with `L` the inner product and `w = -z`.
  have hf (ζ : E) : HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, z⟫ : ℂ)) (c * 𝐞 ⟪ζ, z⟫) ζ v := by
    convert (Real.differentiable_fourierChar_neg_bilinear_left (innerSL ℝ) (-z)
      ζ).hasFDerivAt.hasLineDerivAt v using 1
    · simp only [innerSL_apply_apply ℝ, inner_neg_right, neg_neg]
    · rw [Real.fderiv_fourierChar_neg_bilinear_left_apply]
      simp only [innerSL_apply_apply ℝ, inner_neg_right, neg_neg, Complex.ofReal_neg, c,
        real_inner_comm z v]
      ring
  -- Rescaling the frequency by `2π` multiplies the line derivative by `2π`.
  have hg (ζ : E) : HasLineDerivAt ℝ (fun ζ ↦ a (x, (2 * π) • ζ))
      ((2 * π) • a' (x, (2 * π) • ζ)) ζ v := by
    simpa only [HasLineDerivAt, smul_add, smul_comm (2 * π) _ v] using
      (hda ((2 * π) • ζ)).smul (2 * π)
  -- The kernel integrals written with the complex scalar action of `𝐞`.
  have hK (b : E × E → V →L[ℂ] W) :
      quantizationKernel b x y = ∫ ζ, (𝐞 ⟪ζ, z⟫ : ℂ) • b (x, (2 * π) • ζ) := by
    simp only [quantizationKernel_def, Circle.smul_def, z]
  have hI := integrable_quantizationKernel_integrand ha y
  have hI' := integrable_quantizationKernel_integrand ha' y
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (f := fun ζ ↦ (𝐞 ⟪ζ, z⟫ : ℂ)) (f' := fun ζ ↦ c * 𝐞 ⟪ζ, z⟫)
    (g := fun ζ ↦ a (x, (2 * π) • ζ)) (g' := fun ζ ↦ (2 * π) • a' (x, (2 * π) • ζ))
    ((hI.smul c).congr (ae_of_all _ fun ζ ↦ by
      simp only [Pi.smul_apply, ContinuousLinearMap.lsmul_apply, Circle.smul_def, smul_smul, z]))
    ((hI'.smul (2 * π)).congr (ae_of_all _ fun ζ ↦ by
      simp only [Pi.smul_apply, ContinuousLinearMap.lsmul_apply, Circle.smul_def, z]
      exact smul_comm _ _ _))
    (hI.congr (ae_of_all _ fun ζ ↦ by
      simp only [ContinuousLinearMap.lsmul_apply, Circle.smul_def, z]))
    (fun ζ _ ↦ hf ζ) (fun ζ _ ↦ hg ζ)
  simp only [ContinuousLinearMap.lsmul_apply] at hparts
  have hL : ∫ ζ, (𝐞 ⟪ζ, z⟫ : ℂ) • (2 * π) • a' (x, (2 * π) • ζ) =
      (2 * π) • quantizationKernel a' x y := by
    rw [hK, ← integral_smul]
    congr 1 with ζ
    exact smul_comm _ _ _
  have hR : ∫ ζ, (c * 𝐞 ⟪ζ, z⟫) • a (x, (2 * π) • ζ) = c • quantizationKernel a x y := by
    rw [hK, ← integral_smul]
    congr 1 with ζ
    exact mul_smul _ _ _
  rw [hL, hR] at hparts
  -- `hparts : 2π K_{a'} = -(c K_a)`, with `c = 2πi ⟪v, z⟫`.
  have h2π : (2 * π : ℝ) ≠ 0 := two_pi_pos.ne'
  have hK' : quantizationKernel a' x y = (2 * π)⁻¹ • -(c • quantizationKernel a x y) := by
    rw [← hparts, smul_smul, inv_mul_cancel₀ h2π, one_smul]
  rw [hK']
  simp only [← Complex.coe_smul, smul_smul, ← neg_smul]
  congr 1
  simp only [c, z, real_inner_comm (x - y) v]
  push_cast
  field_simp
  linear_combination (⟪x - y, v⟫ : ℂ) * Complex.I_sq

namespace Symbol

/-! ### Kernels of symbols of order `m < -n` -/

variable {n : ℕ} {m : ℝ}

/-- The frequency slices of a symbol of order `m < -n` are integrable. -/
theorem integrable_coefficient (a : Symbol n V W m) (hm : m < -n) (x : CoordinateSpace n) :
    Integrable (fun ξ ↦ a.coefficient (x, ξ)) := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
  have hweight := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (CoordinateSpace n)))
    (r := -m) (by simp only [finrank_euclideanSpace_fin]; linarith)
  refine (hweight.const_mul C).mono'
    (a.contDiff_coefficient.continuous.comp (continuous_const.prodMk continuous_id)
      ).aestronglyMeasurable (ae_of_all _ fun ξ ↦ ?_)
  simpa only [neg_neg] using hC x rfl ξ

/-- The kernel of a symbol of order `m < -n` is continuous. -/
theorem continuous_quantizationKernel (a : Symbol n V W m) (hm : m < -n) :
    Continuous (Function.uncurry (quantizationKernel a.coefficient)) :=
  TauCeti.continuous_quantizationKernel a.contDiff_coefficient.continuous (by simpa using hm)
    fun K hK ↦ (a.exists_bound_coefficient K hK).imp fun _ h ↦ h.2

/-- **Kernel of a frequency derivative.** For a symbol of order `m < -n`, the kernel of
`∂_{ξ_j} a` is `-i (x - y)_j K_a(x, y)`; equivalently `(x - y)_j K_a = K_{-D_{ξ_j} a}`, where the
coefficient `-D_{ξ_j} a = i ∂_{ξ_j} a` has order `m - 1`. -/
theorem quantizationKernel_frequencyDeriv (a : Symbol n V W m) (hm : m < -n) (j : Fin n)
    (x y : CoordinateSpace n) :
    quantizationKernel (frequencyDeriv j a).coefficient x y =
      -Complex.I • ((x - y) j : ℂ) • quantizationKernel a.coefficient x y := by
  have hda (ξ : CoordinateSpace n) : HasLineDerivAt ℝ (fun ξ ↦ a.coefficient (x, ξ))
      ((frequencyDeriv j a).coefficient (x, ξ)) ξ (EuclideanSpace.single j 1) := by
    rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil]
    exact ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).differentiable
      (by simp) ξ).hasFDerivAt.hasLineDerivAt _
  have h := inner_smul_quantizationKernel hda (a.integrable_coefficient hm x)
    ((frequencyDeriv j a).integrable_coefficient (by linarith) x) y
  rw [EuclideanSpace.inner_single_right, one_mul, conj_trivial] at h
  rw [h, smul_smul]
  simp

/-- **Kernel of an iterated frequency derivative.** For a symbol of order `m < -n`, the kernel of
`∂_{ξ_j}^k a` is `(-i (x - y)_j)^k K_a(x, y)`. -/
theorem quantizationKernel_mixedDeriv_replicate (a : Symbol n V W m) (hm : m < -n) (j : Fin n)
    (k : ℕ) (x y : CoordinateSpace n) :
    quantizationKernel (fun p ↦ mixedDeriv [] (List.replicate k j) a.coefficient p.1 p.2) x y =
      (-Complex.I * ((x - y) j : ℂ)) ^ k • quantizationKernel a.coefficient x y := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    have h : (fun p : CoordinateSpace n × CoordinateSpace n ↦
        mixedDeriv [] (List.replicate (k + 1) j) a.coefficient p.1 p.2) =
        fun p ↦ mixedDeriv [] (List.replicate k j) (frequencyDeriv j a).coefficient p.1 p.2 := by
      funext p
      rw [mixedDeriv_frequencyDeriv, ← List.replicate_succ']
    rw [h, ih (frequencyDeriv j a) (by linarith), quantizationKernel_frequencyDeriv a hm,
      smul_smul, smul_smul, pow_succ, mul_assoc]

/-- For a symbol of order `m < -n`,
`|(x - y)_j|^k ‖K_a(x, y)‖ ≤ (2π)⁻ⁿ ∫ ‖∂_{ξ_j}^k a(x, ξ)‖ dξ`. -/
theorem abs_pow_mul_norm_quantizationKernel_le (a : Symbol n V W m) (hm : m < -n) (j : Fin n)
    (k : ℕ) (x y : CoordinateSpace n) :
    |(x - y) j| ^ k * ‖quantizationKernel a.coefficient x y‖ ≤
      ((2 * π) ^ n)⁻¹ * ∫ ξ, ‖mixedDeriv [] (List.replicate k j) a.coefficient x ξ‖ := by
  have h := norm_quantizationKernel_le
    (fun p ↦ mixedDeriv [] (List.replicate k j) a.coefficient p.1 p.2) x y
  rwa [quantizationKernel_mixedDeriv_replicate a hm, norm_smul, norm_pow, norm_mul, norm_neg,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    finrank_euclideanSpace_fin] at h

/-- **Decay of the kernel off the diagonal.** Let `a` be a symbol of order `m < -n` and `R > 0`. If
at the position `x` the frequency slice has `∫ ‖a(x, ξ)‖ dξ ≤ A` and the `N`-th derivatives in
each frequency coordinate have `∫ ‖∂_{ξ_j}^N a(x, ξ)‖ dξ ≤ A R^N`, then
`(1 + ‖x - y‖ / R)^N ‖K_a(x, y)‖ ≤ 2^N (1 + √n^N) (2π)⁻ⁿ A` for every `y`.

The hypotheses are compatible with the frequency dilations `a(x, ξ) ↦ a(x, ξ / λ)`, `λ > 0`, which
multiply `A` by `λⁿ` and `R` by `λ⁻¹`. For a uniform symbol of order `0` multiplied by smooth
dyadic frequency cutoffs, this makes the estimate uniform over the dyadic pieces and over the
position `x`. -/
theorem one_add_norm_div_pow_mul_norm_quantizationKernel_le (a : Symbol n V W m) (hm : m < -n)
    {x : CoordinateSpace n} {A R : ℝ} (hR : 0 < R) (N : ℕ)
    (h₀ : ∫ ξ, ‖a.coefficient (x, ξ)‖ ≤ A)
    (hN : ∀ j, ∫ ξ, ‖mixedDeriv [] (List.replicate N j) a.coefficient x ξ‖ ≤ A * R ^ N)
    (y : CoordinateSpace n) :
    (1 + ‖x - y‖ / R) ^ N * ‖quantizationKernel a.coefficient x y‖ ≤
      2 ^ N * (1 + √n ^ N) * ((2 * π) ^ n)⁻¹ * A := by
  set K := ‖quantizationKernel a.coefficient x y‖
  set c : ℝ := ((2 * π) ^ n)⁻¹
  have hA : 0 ≤ A := (integral_nonneg fun _ ↦ norm_nonneg _).trans h₀
  have hK₀ : K ≤ c * A := by
    have h := norm_quantizationKernel_le a.coefficient x y
    rw [finrank_euclideanSpace_fin] at h
    exact h.trans (by gcongr)
  -- Away from the diagonal: `(‖x - y‖ / R)^N K ≤ √n^N c A`.
  have hK₁ : (‖x - y‖ / R) ^ N * K ≤ √n ^ N * (c * A) := by
    by_cases hz : x - y = 0
    · rcases N.eq_zero_or_pos with rfl | hN
      · simpa using hK₀
      · rw [hz, norm_zero, zero_div, zero_pow hN.ne', zero_mul]
        positivity
    -- A coordinate of maximal size controls the norm: `‖x - y‖ ≤ √n |(x - y)_j|`.
    have : Nonempty (Fin n) := by
      rcases isEmpty_or_nonempty (Fin n) with h | h
      · exact absurd (Subsingleton.elim _ _) hz
      · exact h
    obtain ⟨j, hj⟩ := Finite.exists_max fun i ↦ |(x - y) i|
    have hnorm : ‖x - y‖ ≤ √n * |(x - y) j| := by
      refine ((EuclideanSpace.basisFun (Fin n) ℝ).norm_le_card_mul_iSup_norm_inner
        (x - y)).trans ?_
      simp only [Fintype.card_fin, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
        map_one, one_mul, Real.norm_eq_abs]
      gcongr
      exact ciSup_le hj
    calc (‖x - y‖ / R) ^ N * K ≤ (√n * |(x - y) j| / R) ^ N * K := by gcongr
      _ = √n ^ N * (|(x - y) j| ^ N * K) / R ^ N := by rw [div_pow, mul_pow]; ring
      _ ≤ √n ^ N * (c * (A * R ^ N)) / R ^ N := by
        gcongr √n ^ N * ?_ / _
        exact (a.abs_pow_mul_norm_quantizationKernel_le hm j N x y).trans (by gcongr; exact hN j)
      _ = √n ^ N * (c * A) := by field_simp
  calc (1 + ‖x - y‖ / R) ^ N * K ≤ 2 ^ N * (1 + (‖x - y‖ / R) ^ N) * K := by
        gcongr
        refine (add_pow_le zero_le_one (by positivity) N).trans ?_
        rw [one_pow]
        gcongr
        exacts [one_le_two, N.sub_le 1]
    _ = 2 ^ N * (K + (‖x - y‖ / R) ^ N * K) := by ring
    _ ≤ 2 ^ N * (c * A + √n ^ N * (c * A)) := by gcongr
    _ = 2 ^ N * (1 + √n ^ N) * c * A := by ring

/-! ### Regularity of the kernel -/

/-- The coefficient whose kernel is the derivative of `K_a` in the direction `v = (h, h')`:
`i ⟪ξ, h - h'⟫ a(x, ξ) + ∂ₓ a(x, ξ) h`, a symbol of order `1 + m`. -/
private def kernelDeriv (a : Symbol n V W m) (v : CoordinateSpace n × CoordinateSpace n) :
    Symbol n V W (1 + m) :=
  Complex.I • (ofInner (v.1 - v.2)).comp a +
    inclusion (by linarith) (∑ j, (v.1 j : ℂ) • spatialDeriv j a)

private theorem coefficient_kernelDeriv (a : Symbol n V W m)
    (v : CoordinateSpace n × CoordinateSpace n) (x ξ : CoordinateSpace n) :
    (kernelDeriv a v).coefficient (x, ξ) =
      (Complex.I * ⟪ξ, v.1 - v.2⟫) • a.coefficient (x, ξ) +
        fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x v.1 := by
  rw [ContinuousLinearMap.apply_eq_sum_single _ v.1]
  simp only [kernelDeriv, coefficient_add, coefficient_smul, coefficient_comp,
    coefficient_ofInner, coefficient_inclusion, coefficient_sum, fderiv_coefficient_single,
    Pi.add_apply, Pi.smul_apply, Finset.sum_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.id_comp]
  rw [mul_smul]
  congr 1

/-- The kernel integrand `𝐞 ⟪ζ, x - y⟫ a(x, 2πζ)` as a function of `p = (x, y)`. -/
private def kernelIntegrand (a : Symbol n V W m) (ζ : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  𝐞 ⟪ζ, p.1 - p.2⟫ • a.coefficient (p.1, (2 * π) • ζ)

/-- The derivative in `p = (x, y)` of the kernel integrand. -/
private def kernelIntegrandFDeriv (a : Symbol n V W m) (ζ : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    CoordinateSpace n × CoordinateSpace n →L[ℝ] V →L[ℂ] W :=
  (𝐞 ⟪ζ, p.1 - p.2⟫ : ℂ) • ((fderiv ℝ (fun y ↦ a.coefficient (y, (2 * π) • ζ)) p.1).comp
      (ContinuousLinearMap.fst ℝ _ _)) +
    ((ContinuousLinearMap.toSpanSingleton ℝ (2 * π * Complex.I * 𝐞 ⟪ζ, p.1 - p.2⟫)).comp
        ((innerSL ℝ ζ).comp
          (ContinuousLinearMap.fst ℝ _ _ - ContinuousLinearMap.snd ℝ _ _))).smulRight
      (a.coefficient (p.1, (2 * π) • ζ))

private theorem kernelIntegrandFDeriv_apply (a : Symbol n V W m) (ζ : CoordinateSpace n)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    kernelIntegrandFDeriv a ζ p v =
      𝐞 ⟪ζ, p.1 - p.2⟫ • (kernelDeriv a v).coefficient (p.1, (2 * π) • ζ) := by
  rw [coefficient_kernelDeriv]
  simp only [kernelIntegrandFDeriv, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Circle.smul_def, smul_add,
    inner_smul_left]
  rw [add_comm]
  congr 1
  simp only [smul_smul]
  congr 1
  simp only [Complex.real_smul, conj_trivial]
  push_cast
  ring

private theorem hasFDerivAt_kernelIntegrand (a : Symbol n V W m) (ζ : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (kernelIntegrand a ζ) (kernelIntegrandFDeriv a ζ p) p := by
  have hg : HasFDerivAt (fun q : CoordinateSpace n × CoordinateSpace n ↦
      a.coefficient (q.1, (2 * π) • ζ))
      ((fderiv ℝ (fun y ↦ a.coefficient (y, (2 * π) • ζ)) p.1).comp
        (ContinuousLinearMap.fst ℝ _ _)) p :=
    (((a.contDiff_coefficient_slice _).differentiable (by simp) p.1).hasFDerivAt).comp p
      (hasFDerivAt_fst)
  have hL : HasFDerivAt (fun q : CoordinateSpace n × CoordinateSpace n ↦ ⟪ζ, q.1 - q.2⟫)
      ((innerSL ℝ ζ).comp (ContinuousLinearMap.fst ℝ _ _ - ContinuousLinearMap.snd ℝ _ _)) p :=
    ((innerSL ℝ ζ).comp (ContinuousLinearMap.fst ℝ _ _ - ContinuousLinearMap.snd ℝ _ _)).hasFDerivAt
  have hc := (Real.hasDerivAt_fourierChar ⟪ζ, p.1 - p.2⟫).hasFDerivAt.comp p hL
  convert hc.smul hg using 1
  · funext q
    simp [kernelIntegrand, Circle.smul_def]
  · simp [kernelIntegrandFDeriv]

/-- The coefficient of `kernelDeriv a v` at `x` is bounded by `(C' + 2C) ⟨ξ⟩ ^ (m + 1) ‖v‖` when
the values and position derivatives of `a` at `x` are bounded by `C ⟨ξ⟩ ^ m` and `C' ⟨ξ⟩ ^ m`. -/
private theorem norm_coefficient_kernelDeriv_le (a : Symbol n V W m) {x : CoordinateSpace n}
    {C C' : ℝ} (hC : ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ ξ, ‖fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (v : CoordinateSpace n × CoordinateSpace n) (ξ : CoordinateSpace n) :
    ‖(kernelDeriv a v).coefficient (x, ξ)‖ ≤
      (C' + 2 * C) * (1 + ‖ξ‖ ^ 2) ^ ((m + 1) / 2) * ‖v‖ := by
  have hC0 : 0 ≤ C :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC 0)) (rpow_weight_pos _ _)
  have hC'0 : 0 ≤ C' := nonneg_of_mul_nonneg_left
    ((norm_nonneg (fderiv ℝ (fun y ↦ a.coefficient (y, 0)) x)).trans (hC' 0)) (rpow_weight_pos _ _)
  set w := 1 + ‖ξ‖ ^ 2
  have hw : w ^ (m / 2) ≤ w ^ ((m + 1) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)
  have hw' := one_add_norm_sq_rpow_mul_norm_le ξ m
  have hv : ‖v.1 - v.2‖ ≤ 2 * ‖v‖ := by
    linarith [norm_sub_le v.1 v.2, norm_fst_le v, norm_snd_le v]
  rw [coefficient_kernelDeriv]
  refine (norm_add_le _ _).trans ?_
  have h₁ : ‖(Complex.I * ⟪ξ, v.1 - v.2⟫) • a.coefficient (x, ξ)‖ ≤
      2 * C * w ^ ((m + 1) / 2) * ‖v‖ := by
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |⟪ξ, v.1 - v.2⟫| * ‖a.coefficient (x, ξ)‖
        ≤ (‖ξ‖ * (2 * ‖v‖)) * (C * w ^ (m / 2)) := by
          gcongr
          · exact (abs_real_inner_le_norm _ _).trans (by gcongr)
          · exact hC ξ
      _ = 2 * C * (w ^ (m / 2) * ‖ξ‖) * ‖v‖ := by ring
      _ ≤ 2 * C * w ^ ((m + 1) / 2) * ‖v‖ := by gcongr
  have h₂ : ‖fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x v.1‖ ≤ C' * w ^ ((m + 1) / 2) * ‖v‖ :=
    calc _ ≤ ‖fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x‖ * ‖v.1‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C' * w ^ (m / 2) * ‖v‖ := by gcongr; exacts [hC' ξ, norm_fst_le v]
      _ ≤ C' * w ^ ((m + 1) / 2) * ‖v‖ := by gcongr
  linarith

/-- The kernel of `a` is the parametric integral of the kernel integrand. -/
private theorem uncurry_quantizationKernel_eq (a : Symbol n V W m) :
    Function.uncurry (quantizationKernel a.coefficient) = fun p ↦ ∫ ζ, kernelIntegrand a ζ p := by
  funext p
  exact quantizationKernel_def _ _ _

/-- The derivative of the kernel integrand is bounded by `(C' + 2C) ⟨2πζ⟩ ^ (m + 1)` when the values
and position derivatives of `a` at `x` are bounded by `C ⟨ξ⟩ ^ m` and `C' ⟨ξ⟩ ^ m`. -/
private theorem norm_kernelIntegrandFDeriv_le (a : Symbol n V W m) {x : CoordinateSpace n}
    {C C' : ℝ} (hC : ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ ξ, ‖fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (y ζ : CoordinateSpace n) :
    ‖kernelIntegrandFDeriv a ζ (x, y)‖ ≤
      (C' + 2 * C) * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m + 1) / 2) := by
  have hC0 : 0 ≤ C :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC 0)) (rpow_weight_pos _ _)
  have hC'0 : 0 ≤ C' := nonneg_of_mul_nonneg_left
    ((norm_nonneg (fderiv ℝ (fun y ↦ a.coefficient (y, 0)) x)).trans (hC' 0)) (rpow_weight_pos _ _)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [kernelIntegrandFDeriv_apply, Circle.norm_smul (E := V →L[ℂ] W)]
  exact norm_coefficient_kernelDeriv_le a hC hC' v _

private theorem continuous_kernelIntegrand (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) : Continuous fun ζ ↦ kernelIntegrand a ζ p :=
  (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
    (a.contDiff_coefficient.continuous.comp (continuous_const.prodMk (continuous_const_smul _)))

private theorem aestronglyMeasurable_kernelIntegrandFDeriv (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    AEStronglyMeasurable fun ζ ↦ kernelIntegrandFDeriv a ζ p := by
  have hcont : Continuous fun ζ ↦ kernelIntegrandFDeriv a ζ p := by
    refine continuous_clm_apply.2 fun v ↦ ?_
    simp only [kernelIntegrandFDeriv_apply]
    exact (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      ((kernelDeriv a v).contDiff_coefficient.continuous.comp
        (continuous_const.prodMk (continuous_const_smul _)))
  -- Instance search does not find the metrizability of this space of operators unaided.
  let _ : PseudoMetricSpace (CoordinateSpace n × CoordinateSpace n →L[ℝ] V →L[ℂ] W) :=
    inferInstance
  exact hcont.aestronglyMeasurable

/-- **Differentiation of the kernel.** For a symbol of order `m < -n - 1`, the kernel is
differentiable, and its derivative is the integral of the derivative of the integrand. -/
private theorem hasFDerivAt_quantizationKernel (a : Symbol n V W m) (hm : m + 1 < -n)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (Function.uncurry (quantizationKernel a.coefficient))
      (∫ ζ, kernelIntegrandFDeriv a ζ p₀) p₀ := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient _ (isCompact_closedBall p₀.1 1)
  obtain ⟨C', hC'⟩ := a.exists_bound_fderiv_coefficient _ (isCompact_closedBall p₀.1 1)
  have hmem : ∀ p ∈ Metric.ball p₀ 1, p.1 ∈ Metric.closedBall p₀.1 1 := fun p hp ↦
    Metric.mem_closedBall.2
    (((le_max_left _ _).trans (Prod.dist_eq (x := p) (y := p₀)).ge).trans (Metric.mem_ball.1 hp).le)
  rw [uncurry_quantizationKernel_eq]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ one_pos)
    (Filter.Eventually.of_forall fun p ↦ (continuous_kernelIntegrand a p).aestronglyMeasurable)
    (integrable_quantizationKernel_integrand (a.integrable_coefficient (by linarith) p₀.1) p₀.2)
    (aestronglyMeasurable_kernelIntegrandFDeriv a p₀)
    (ae_of_all _ fun ζ p hp ↦ norm_kernelIntegrandFDeriv_le a (hC p.1 (hmem p hp))
      (hC' p.1 (hmem p hp)) p.2 ζ)
    ((integrable_one_add_norm_two_pi_smul_sq_rpow (s := m + 1) (by simpa using hm)).const_mul
      (C' + 2 * C))
    (ae_of_all _ fun ζ p _ ↦ hasFDerivAt_kernelIntegrand a ζ p)

/-- The derivative of the kernel in the direction `v` is the kernel of `kernelDeriv a v`. -/
private theorem fderiv_quantizationKernel_apply (a : Symbol n V W m) (hm : m + 1 < -n)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (Function.uncurry (quantizationKernel a.coefficient)) p v =
      quantizationKernel (kernelDeriv a v).coefficient p.1 p.2 := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient _ (isCompact_singleton (x := p.1))
  obtain ⟨C', hC'⟩ := a.exists_bound_fderiv_coefficient _ (isCompact_singleton (x := p.1))
  -- Instance search does not find the norm structure of this space of operators unaided.
  let _ : NormedAddCommGroup (CoordinateSpace n × CoordinateSpace n →L[ℝ] V →L[ℂ] W) :=
    inferInstance
  have hint : Integrable fun ζ ↦ kernelIntegrandFDeriv a ζ p :=
    ((integrable_one_add_norm_two_pi_smul_sq_rpow (s := m + 1) (by simpa using hm)).const_mul
      (C' + 2 * C)).mono'
      (aestronglyMeasurable_kernelIntegrandFDeriv a p)
      (ae_of_all _ fun ζ ↦ norm_kernelIntegrandFDeriv_le a (hC p.1 rfl) (hC' p.1 rfl) p.2 ζ)
  rw [(hasFDerivAt_quantizationKernel a hm p).fderiv, ContinuousLinearMap.integral_apply hint,
    quantizationKernel_def]
  simp only [kernelIntegrandFDeriv_apply]

/-- **Regularity of the kernel.** The kernel `(x, y) ↦ K_a(x, y)` of a symbol of order `m` with
`m + k < -n` is `C^k`. -/
theorem contDiff_quantizationKernel (k : ℕ) (a : Symbol n V W m) (hm : m + k < -n) :
    ContDiff ℝ k (Function.uncurry (quantizationKernel a.coefficient)) := by
  induction k generalizing m with
  | zero => exact contDiff_zero.2 (a.continuous_quantizationKernel (by simpa using hm))
  | succ k ih =>
    have hm' : m + 1 < -n := by push_cast at hm; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun p ↦ (hasFDerivAt_quantizationKernel a hm' p).differentiableAt, by simp,
      contDiff_clm_apply_iff.2 fun v ↦ ?_⟩
    simp only [fderiv_quantizationKernel_apply a hm']
    exact ih (kernelDeriv a v) (by push_cast at hm; linarith)

/-- **Smoothness of smoothing kernels.** The kernel of a smoothing symbol is smooth. -/
theorem IsSmoothing.contDiff_quantizationKernel {a : Symbol n V W m} (ha : a.IsSmoothing) :
    ContDiff ℝ ∞ (Function.uncurry (quantizationKernel a.coefficient)) := by
  refine contDiff_infty.2 fun k ↦ ?_
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha (-n - k - 1)
  rw [← hb]
  exact b.contDiff_quantizationKernel k (by linarith)

/-- The kernel is additive over finite sums of symbols of order `m < -n`. -/
theorem quantizationKernel_sum {ι : Type*} (s : Finset ι) (a : ι → Symbol n V W m)
    (hm : m < -n) (x y : CoordinateSpace n) :
    quantizationKernel (∑ i ∈ s, a i).coefficient x y =
      ∑ i ∈ s, quantizationKernel (a i).coefficient x y := by
  simp only [quantizationKernel_def, coefficient_sum, Finset.sum_apply]
  rw [← integral_finsetSum s fun i _ ↦
    integrable_quantizationKernel_integrand ((a i).integrable_coefficient hm x) y]
  congr 1 with ζ
  simp only [Circle.smul_def, Finset.smul_sum]

/-- **Multiplication by the squared displacement.** For a symbol of order `m < -n`, multiplying the
kernel by `‖x - y‖²` gives the kernel of `-Δ_ξ a`, a symbol of order `m - 2`. -/
theorem norm_sq_smul_quantizationKernel (a : Symbol n V W m) (hm : m < -n)
    (x y : CoordinateSpace n) :
    ‖x - y‖ ^ 2 • quantizationKernel a.coefficient x y =
      quantizationKernel (-frequencyLaplacian a).coefficient x y := by
  have hj (j : Fin n) : quantizationKernel
      (inclusion (show m - 1 - 1 ≤ m - 2 by linarith)
        (frequencyDeriv j (frequencyDeriv j a))).coefficient x y =
      -((x - y) j ^ 2 : ℝ) • quantizationKernel a.coefficient x y := by
    rw [coefficient_inclusion, quantizationKernel_frequencyDeriv _ (by linarith),
      quantizationKernel_frequencyDeriv _ hm, ← Complex.coe_smul]
    simp only [smul_smul]
    congr 1
    push_cast
    linear_combination ((x - y) j : ℂ) ^ 2 * Complex.I_sq
  rw [coefficient_neg, ← neg_one_smul ℂ (frequencyLaplacian a).coefficient, quantizationKernel_smul,
    neg_one_smul, frequencyLaplacian_apply, quantizationKernel_sum _ _ (by linarith)]
  simp only [hj, ← Finset.sum_smul, EuclideanSpace.real_norm_sq_eq, neg_smul,
    Finset.sum_neg_distrib, neg_neg]

/-- `(-Δ_ξ)^N a`, a symbol of order `m - 2N`. -/
private def negFrequencyLaplacianPow (a : Symbol n V W m) : (N : ℕ) → Symbol n V W (m - 2 * N)
  | 0 => inclusion (by simp) a
  | N + 1 => inclusion (by push_cast; linarith) (-frequencyLaplacian (negFrequencyLaplacianPow a N))

private theorem coefficient_negFrequencyLaplacianPow_zero (a : Symbol n V W m) :
    (negFrequencyLaplacianPow a 0).coefficient = a.coefficient := by
  simp [negFrequencyLaplacianPow]

private theorem coefficient_negFrequencyLaplacianPow_succ (a : Symbol n V W m) (N : ℕ) :
    (negFrequencyLaplacianPow a (N + 1)).coefficient =
      (-frequencyLaplacian (negFrequencyLaplacianPow a N)).coefficient := by
  simp [negFrequencyLaplacianPow]

/-- For a symbol `a` of order `m < -n`, `‖x - y‖^(2N) K_a(x, y)` is the kernel of `(-Δ_ξ)^N a`. -/
private theorem norm_sq_pow_smul_quantizationKernel (a : Symbol n V W m) (hm : m < -n) (N : ℕ)
    (x y : CoordinateSpace n) :
    (‖x - y‖ ^ 2) ^ N • quantizationKernel a.coefficient x y =
      quantizationKernel (negFrequencyLaplacianPow a N).coefficient x y := by
  induction N with
  | zero => simp [coefficient_negFrequencyLaplacianPow_zero]
  | succ N ih =>
    have hNm : m - 2 * N < -n := by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
    rw [coefficient_negFrequencyLaplacianPow_succ,
      ← norm_sq_smul_quantizationKernel _ hNm, ← ih, smul_smul, pow_succ, mul_comm]

/-- **Smoothness off the diagonal.** The kernel of a symbol of order `m < -n` is smooth off the
diagonal `x = y`. -/
theorem contDiffOn_quantizationKernel (a : Symbol n V W m) (hm : m < -n) :
    ContDiffOn ℝ ∞ (Function.uncurry (quantizationKernel a.coefficient)) {p | p.1 ≠ p.2} := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_gt ((m + k + n) / 2)
  set b := negFrequencyLaplacianPow a N
  have hb := norm_sq_pow_smul_quantizationKernel a hm N
  have hw : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦ (‖p.1 - p.2‖ ^ 2) ^ N :=
    ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).pow N
  have hne : ∀ p ∈ {p : CoordinateSpace n × CoordinateSpace n | p.1 ≠ p.2},
      (‖p.1 - p.2‖ ^ 2) ^ N ≠ 0 := fun p hp ↦
    pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hp)))
  refine ContDiffOn.congr (f := fun p ↦ ((‖p.1 - p.2‖ ^ 2) ^ N)⁻¹ •
      Function.uncurry (quantizationKernel b.coefficient) p)
    (((hw.of_le (mod_cast le_top)).contDiffOn.inv hne).smul
      (b.contDiff_quantizationKernel k (by linarith)).contDiffOn) fun p hp ↦ ?_
  obtain ⟨x, y⟩ := p
  simp only [Function.uncurry_apply_pair]
  rw [← hb, smul_smul, inv_mul_cancel₀ (hne _ hp), one_smul]

private theorem hasTemperateGrowth_norm_sub_sq_pow (x : CoordinateSpace n) (N : ℕ) :
    (fun y : CoordinateSpace n ↦ (‖x - y‖ ^ 2) ^ N).HasTemperateGrowth :=
  ((Function.hasTemperateGrowth_norm_sq _).comp (by fun_prop :
    (fun y : CoordinateSpace n ↦ x - y).HasTemperateGrowth)).pow N

/-- Multiplying the input by `‖x - y‖^(2N)` before quantizing at `x` gives the quantization at `x`
of `(-Δ_ξ)^N a`. -/
private theorem quantizeSchwartzValue_smulLeftCLM_norm_sub_sq_pow (a : Symbol n V W m) (N : ℕ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (‖x - y‖ ^ 2) ^ N) u) x =
      quantizeSchwartzValue (negFrequencyLaplacianPow a N).coefficient u x := by
  induction N generalizing u with
  | zero => simp [coefficient_negFrequencyLaplacianPow_zero]
  | succ N ih =>
    have hg : (fun y : CoordinateSpace n ↦ (‖x - y‖ ^ 2) ^ (N + 1)) =
        (fun y : CoordinateSpace n ↦ (‖x - y‖ ^ 2) ^ N) * fun y ↦ ‖x - y‖ ^ 2 := by
      funext y
      simp [pow_succ]
    rw [hg, ← SchwartzMap.smulLeftCLM_smulLeftCLM_apply (hasTemperateGrowth_norm_sub_sq_pow x N)
      (by simpa using hasTemperateGrowth_norm_sub_sq_pow x 1), ih,
      quantizeSchwartzValue_smulLeftCLM_norm_sub_sq, coefficient_negFrequencyLaplacianPow_succ,
      coefficient_neg, ← neg_one_smul ℂ (frequencyLaplacian _).coefficient,
      quantizeSchwartzValue_smul_left, neg_one_smul]

/-- The number `N = ⌈(m + n) / 2⌉₊ + 1` of factors `‖x - y‖²` used to define the off-diagonal
kernel: `(-Δ_ξ)^N a` then has order `m - 2N < -n`. -/
private theorem order_sub_two_mul_lt (m : ℝ) (n : ℕ) :
    m - 2 * ((⌈(m + n) / 2⌉₊ + 1 : ℕ) : ℝ) < -n := by
  have := Nat.le_ceil ((m + n) / 2)
  push_cast
  linarith

/-- **The kernel off the diagonal.** For a symbol `a` of any order `m`, the function
`K(x, y) = ‖x - y‖^(-2N) K_{(-Δ_ξ)^N a}(x, y)` with `N = ⌈(m + n) / 2⌉₊ + 1`, where
`(-Δ_ξ)^N a` has order `m - 2N < -n` and therefore an absolutely convergent kernel. Away from the
diagonal it is the distribution kernel of the quantization of `a`
(`TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`), it is smooth there
(`TauCeti.Symbol.contDiffOn_offDiagonalKernel`), and for `m < -n` it agrees with the kernel `K_a`
(`TauCeti.Symbol.offDiagonalKernel_eq_quantizationKernel`). On the diagonal it has the junk
value `0`. -/
def offDiagonalKernel (a : Symbol n V W m) (x y : CoordinateSpace n) : V →L[ℂ] W :=
  ((‖x - y‖ ^ 2) ^ (⌈(m + n) / 2⌉₊ + 1))⁻¹ •
    quantizationKernel (negFrequencyLaplacianPow a (⌈(m + n) / 2⌉₊ + 1)).coefficient x y

/-- The kernel off the diagonal is smooth on `{(x, y) | x ≠ y}`. -/
theorem contDiffOn_offDiagonalKernel (a : Symbol n V W m) :
    ContDiffOn ℝ ∞ (Function.uncurry (offDiagonalKernel a)) {p | p.1 ≠ p.2} := by
  set N := ⌈(m + n) / 2⌉₊ + 1
  have hw : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦ (‖p.1 - p.2‖ ^ 2) ^ N :=
    ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).pow N
  have hne : ∀ p ∈ {p : CoordinateSpace n × CoordinateSpace n | p.1 ≠ p.2},
      (‖p.1 - p.2‖ ^ 2) ^ N ≠ 0 := fun p hp ↦
    pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hp)))
  exact ((hw.contDiffOn.inv hne).smul
    ((negFrequencyLaplacianPow a N).contDiffOn_quantizationKernel (order_sub_two_mul_lt m n)))

/-- For a symbol of order `m < -n`, the kernel off the diagonal is the kernel `K_a`. -/
theorem offDiagonalKernel_eq_quantizationKernel (a : Symbol n V W m) (hm : m < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = quantizationKernel a.coefficient x y := by
  have hne : (‖x - y‖ ^ 2) ^ (⌈(m + n) / 2⌉₊ + 1) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)))
  rw [offDiagonalKernel, ← norm_sq_pow_smul_quantizationKernel a hm, smul_smul,
    inv_mul_cancel₀ hne, one_smul]

/-- **Kernel representation off the diagonal.** For a symbol `a` of any order and a compactly
supported Schwartz function `u` that vanishes near `x`, the quantization is given by the kernel
off the diagonal: `Op(a) u (x) = ∫ K(x, y) u(y) dy`. -/
theorem quantizeSchwartzValue_eq_integral_offDiagonalKernel [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u)
    {x : CoordinateSpace n} (hx : x ∉ tsupport u) :
    quantizeSchwartzValue a.coefficient u x = ∫ y, offDiagonalKernel a x y (u y) := by
  set N := ⌈(m + n) / 2⌉₊ + 1
  set g : CoordinateSpace n → ℝ := fun y ↦ (‖x - y‖ ^ 2) ^ N
  have hg0 : ∀ y ∈ tsupport u, g y ≠ 0 := fun y hy ↦
    pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 fun h ↦ hx (h ▸ hy))))
  -- divide `u` by `g`, which vanishes only at `x`, away from the support of `u`
  have hsmooth : ContDiff ℝ ∞ fun y ↦ (g y)⁻¹ • u y := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ tsupport u
    · have hgc : ContDiff ℝ ∞ g :=
        ((contDiff_norm_sq ℝ).comp (contDiff_const.sub contDiff_id)).pow N
      exact (hgc.contDiffAt.inv (hg0 y hy)).smul u.smooth'.contDiffAt
    · refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy] with z hz
      simp [hz]
  set v : 𝓢(CoordinateSpace n, V) := (hu.smul_left (f := fun y ↦ (g y)⁻¹)).toSchwartzMap hsmooth
  have hv : SchwartzMap.smulLeftCLM V g v = u := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_norm_sub_sq_pow x N),
      HasCompactSupport.toSchwartzMap_toFun, Pi.smul_apply']
    by_cases hy : y ∈ tsupport u
    · exact smul_inv_smul₀ (hg0 y hy) _
    · rw [image_eq_zero_of_notMem_tsupport hy, smul_zero, smul_zero]
  conv_lhs => rw [← hv]
  rw [quantizeSchwartzValue_smulLeftCLM_norm_sub_sq_pow,
    quantizeSchwartzValue_eq_integral_quantizationKernel
      ((negFrequencyLaplacianPow a N).integrable_coefficient (order_sub_two_mul_lt m n) x)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp [offDiagonalKernel, v, HasCompactSupport.toSchwartzMap_toFun, g, N]

/-- A kernel continuous away from `x` integrates against a compactly supported Schwartz function
vanishing near `x`. -/
private theorem integrable_apply_of_continuousOn {x : CoordinateSpace n}
    {L : CoordinateSpace n → V →L[ℂ] W} (hL : ContinuousOn L {x}ᶜ)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) (hx : x ∉ tsupport u) :
    Integrable fun y ↦ L y (u y) := by
  refine Continuous.integrable_of_hasCompactSupport
    (continuous_iff_continuousAt.2 fun z ↦ ?_) (hu.mono fun y hy h0 ↦ hy (by simp [h0]))
  by_cases hz : z = x
  · subst hz
    refine continuousAt_const.congr (f := fun _ ↦ (0 : W)) ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
    simp [hy]
  · exact (hL.continuousAt (isOpen_compl_singleton.mem_nhds hz)).clm_apply
      u.continuous.continuousAt

/-- **Uniqueness of the kernel off the diagonal.** A kernel `K`, continuous away from `x`, that
represents `u ↦ Op(a) u (x)` on the compactly supported Schwartz functions vanishing near `x` is the
kernel off the diagonal: `K y = offDiagonalKernel a x y` for every `y ≠ x`. In particular the
definition of `offDiagonalKernel` does not depend on the number of factors `‖x - y‖²` it uses. -/
theorem eqOn_offDiagonalKernel_of_forall [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    {x : CoordinateSpace n} {K : CoordinateSpace n → V →L[ℂ] W} (hK : ContinuousOn K {x}ᶜ)
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u → x ∉ tsupport u →
      quantizeSchwartzValue a.coefficient u x = ∫ y, K y (u y)) :
    Set.EqOn K (offDiagonalKernel a x) {x}ᶜ := by
  have hU : IsOpen ({x}ᶜ : Set (CoordinateSpace n)) := isOpen_compl_singleton
  have hK₀ : ContinuousOn (offDiagonalKernel a x) {x}ᶜ := by
    have hmaps : Set.MapsTo (fun y ↦ (x, y)) {x}ᶜ
        {p : CoordinateSpace n × CoordinateSpace n | p.1 ≠ p.2} := fun y hy ↦ Ne.symm hy
    have h' := (contDiffOn_offDiagonalKernel a).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmaps
    exact h'.congr fun y _ ↦ (Function.uncurry_apply_pair _ x y).symm
  intro y hy
  ext v
  set f : CoordinateSpace n → W := fun z ↦ K z v - offDiagonalKernel a x z v
  have hf : ContinuousOn f {x}ᶜ :=
    (hK.clm_apply continuousOn_const).sub (hK₀.clm_apply continuousOn_const)
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hf.locallyIntegrableOn hU.measurableSet) fun g hg hgs hgU ↦ ?_
  · have hEq := Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae) hU hf
      continuousOn_const hy
    exact sub_eq_zero.1 hEq
  · have hgc : ContDiff ℝ ∞ (fun z ↦ (g z : ℂ) • v) :=
      (Complex.ofRealCLM.contDiff.comp hg).smul contDiff_const
    have hgcs : HasCompactSupport (fun z ↦ (g z : ℂ) • v) :=
      (hgs.comp_left Complex.ofReal_zero).smul_right
    set u := hgcs.toSchwartzMap hgc
    have hu : HasCompactSupport u := hgcs
    have hcoe : (u : CoordinateSpace n → V) = fun z ↦ (g z : ℂ) • v :=
      funext fun z ↦ HasCompactSupport.toSchwartzMap_toFun _ _ z
    have hxu : x ∉ tsupport u := fun hx ↦ by
      rw [hcoe] at hx
      exact hgU (((tsupport_smul_subset_left _ _).trans
        (tsupport_comp_subset Complex.ofReal_zero g)) hx) rfl
    have hpt (L : CoordinateSpace n → V →L[ℂ] W) (z : CoordinateSpace n) :
        g z • L z v = L z (u z) := by
      rw [HasCompactSupport.toSchwartzMap_toFun, map_smul, Complex.coe_smul]
    simp only [f, smul_sub, hpt K, hpt (offDiagonalKernel a x)]
    rw [integral_sub (integrable_apply_of_continuousOn hK hu hxu)
      (integrable_apply_of_continuousOn hK₀ hu hxu), ← h u hu hxu,
      ← quantizeSchwartzValue_eq_integral_offDiagonalKernel a hu hxu, sub_self]

end Symbol

end TauCeti
