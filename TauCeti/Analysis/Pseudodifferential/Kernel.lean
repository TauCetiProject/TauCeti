/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv

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
* `TauCeti.contDiff_quantizationKernel_of_bound` and `TauCeti.Symbol.contDiff_quantizationKernel`:
  **smoothness**, the kernel of a coefficient of order `m` is `C^k` when `m + k < -n`; each
  derivative of the integrand in `(x, y)` costs one power of the frequency.
* `TauCeti.Symbol.quantizationKernel_frequencyLaplacian`: for `m < -n`, the kernel of the
  frequency Laplacian `Δ_ξ a` is `-‖x - y‖² K_a(x, y)`;
  `TauCeti.Symbol.quantizationKernel_iteratedFrequencyLaplacian` iterates this.

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

/-- The kernel is additive over finite sums of coefficients at every position where all the
frequency slices are integrable. -/
theorem quantizationKernel_sum {ι : Type*} (s : Finset ι) {a : ι → E × E → V →L[ℂ] W}
    (ha : ∀ i ∈ s, Integrable (fun ξ ↦ a i (x, ξ))) (y : E) :
    quantizationKernel (∑ i ∈ s, a i) x y = ∑ i ∈ s, quantizationKernel (a i) x y := by
  simp only [quantizationKernel_def, Finset.sum_apply, Circle.smul_def, Finset.smul_sum]
  exact integral_finsetSum s fun i hi ↦ by
    simpa only [Circle.smul_def] using integrable_quantizationKernel_integrand (ha i hi) y

/-- **Continuity in the second variable.** If the frequency slice `ξ ↦ a(x, ξ)` is integrable, then
`y ↦ K_a(x, y)` is continuous. -/
theorem continuous_quantizationKernel_right (ha : Integrable (fun ξ ↦ a (x, ξ))) :
    Continuous (quantizationKernel a x) := by
  rw [funext (quantizationKernel_eq_fourierInv a x)]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner.neg (ha.comp_smul two_pi_pos.ne')).comp (continuous_const.sub continuous_id)

/-- **Joint continuity.** For a continuous coefficient whose growth bound
`‖a(x, ξ)‖ ≤ C_K ⟨ξ⟩ ^ m` with `m < -n` is uniform for `x` in each compact set `K`, the kernel
`(x, y) ↦ K_a(x, y)` is continuous. -/
theorem continuous_quantizationKernel (ha : Continuous a) {m : ℝ} (hm : m < -finrank ℝ E)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    Continuous (Function.uncurry (quantizationKernel a)) := by
  have hweight : Integrable (fun ζ : E ↦ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2)) := by
    have h := (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure E))
      (r := -m) (by linarith)).comp_smul two_pi_pos.ne'
    simpa only [neg_neg] using h
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

/-- The phase `(x, y) ↦ 2πi ⟪ζ, x - y⟫` of the kernel integrand at the frequency `ζ`, a real-linear
map to `ℂ` of norm at most `2 ‖2πζ‖`. -/
private def kernelPhase (ζ : E) : E × E →L[ℝ] ℂ :=
  ((2 * π : ℂ) * Complex.I) • (Complex.ofRealCLM ∘L (innerSL ℝ ζ) ∘L
    (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem kernelPhase_apply (ζ : E) (p : E × E) :
    kernelPhase ζ p = ((2 * π * ⟪ζ, p.1 - p.2⟫ : ℝ) : ℂ) * Complex.I := by
  simp [kernelPhase, inner_sub_right]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem exp_kernelPhase (ζ : E) (p : E × E) :
    Complex.exp (kernelPhase ζ p) = 𝐞 ⟪ζ, p.1 - p.2⟫ := by
  rw [kernelPhase_apply, Real.fourierChar_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_kernelPhase_le (ζ : E) : ‖kernelPhase ζ‖ ≤ 2 * ‖(2 * π) • ζ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p ↦ ?_
  rw [kernelPhase_apply, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos two_pi_pos, norm_smul, Real.norm_of_nonneg two_pi_pos.le]
  have hp : ‖p.1 - p.2‖ ≤ 2 * ‖p‖ := (norm_sub_le _ _).trans (by
    linarith [norm_fst_le p, norm_snd_le p])
  calc 2 * π * |⟪ζ, p.1 - p.2⟫| ≤ 2 * π * (‖ζ‖ * ‖p.1 - p.2‖) := by
        gcongr; exact abs_real_inner_le_norm _ _
    _ ≤ 2 * π * (‖ζ‖ * (2 * ‖p‖)) := by gcongr
    _ = 2 * (2 * π * ‖ζ‖) * ‖p‖ := by ring

/-- **Smoothness of the kernel.** Let `a` be a `C^k` coefficient whose position derivatives of
order at most `k` satisfy `‖D_x^i a(x, ξ)‖ ≤ C_K ⟨ξ⟩ ^ m`, uniformly for `x` in each compact set
`K`, with `m + k < -n`. Then the kernel `(x, y) ↦ K_a(x, y)` is `C^k`: each derivative of the
integrand `exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ)` in `(x, y)` costs at most one power of `⟨2πζ⟩`. -/
theorem contDiff_quantizationKernel_of_bound {a : E × E → V →L[ℂ] W} {k : ℕ} {m : ℝ}
    (ha : ContDiff ℝ k a) (hm : m + k < -finrank ℝ E)
    (hC : ∀ K : Set E, IsCompact K → ∃ C, ∀ i ≤ k, ∀ x ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun y ↦ a (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    ContDiff ℝ k (Function.uncurry (quantizationKernel a)) := by
  -- Near each point `p₀`, Mathlib's `hasFTaylorSeriesUpToOn_integral_of_le_bound` differentiates
  -- under the integral sign `k` times. Its hypotheses are measurability of the derivatives of the
  -- integrand in the frequency, the Leibniz bound `C (1 + 2 ‖2πζ‖) ^ i ⟨2πζ⟩ ^ m` on the `i`-th
  -- derivative for positions near `p₀`, and integrability of these bounds since `m + k < -n`.
  -- The integrand `F p ζ` as a jointly `C^k` function of the kernel variables `p = (x, y)` and the
  -- frequency `ζ`.
  obtain ⟨F, hF⟩ : ∃ F : E × E → E → V →L[ℂ] W,
      F = fun p ζ ↦ Complex.exp (kernelPhase ζ p) • a (p.1, (2 * π) • ζ) := ⟨_, rfl⟩
  have hK : Function.uncurry (quantizationKernel a) = fun p ↦ ∫ ζ, F p ζ := by
    funext p
    simp only [Function.uncurry_def, quantizationKernel_def, hF, exp_kernelPhase, Circle.smul_def]
  have hΦ : ContDiff ℝ k fun q : (E × E) × E ↦ F q.1 q.2 := by
    have hphase : ContDiff ℝ k fun q : (E × E) × E ↦ (2 * π * ⟪q.2, q.1.1 - q.1.2⟫ : ℝ) :=
      contDiff_const.mul (contDiff_snd.inner ℝ
        ((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst)))
    simp only [hF, kernelPhase_apply]
    exact ((Complex.ofRealCLM.contDiff.comp hphase).mul contDiff_const).cexp.smul
      (ha.comp ((contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.const_smul _)))
  have hslice (ζ : E) : ContDiff ℝ k fun p ↦ F p ζ :=
    hΦ.comp (contDiff_id.prodMk contDiff_const)
  rw [hK, contDiff_iff_contDiffAt]
  intro p₀
  obtain ⟨C, hC⟩ := hC _ (isCompact_closedBall p₀.1 1)
  have hs : IsOpen (Prod.fst ⁻¹' Metric.ball p₀.1 1 : Set (E × E)) :=
    Metric.isOpen_ball.preimage continuous_fst
  -- The derivatives of the slice `p ↦ F p ζ` are those of the jointly smooth integrand.
  have hslice_deriv (ζ : E) (i : ℕ) (hi : i ≤ k) (p : E × E) :
      iteratedFDeriv ℝ i (F · ζ) p = (iteratedFDeriv ℝ i (fun q : (E × E) × E ↦ F q.1 q.2)
        (p, ζ)).compContinuousLinearMap fun _ ↦ ContinuousLinearMap.inl ℝ (E × E) E := by
    have h : (F · ζ) = (fun q : (E × E) × E ↦ F (q + (0, ζ)).1 (q + (0, ζ)).2) ∘
        ContinuousLinearMap.inl ℝ (E × E) E := by
      funext p
      simp
    have hg : ContDiff ℝ k fun q : (E × E) × E ↦ F (q + (0, ζ)).1 (q + (0, ζ)).2 :=
      hΦ.comp (contDiff_id.add contDiff_const)
    have hshift := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun q : (E × E) × E ↦ F q.1 q.2)
      i (0, ζ) (ContinuousLinearMap.inl ℝ (E × E) E p)
    rw [h, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (mod_cast hi), hshift]
    simp
  -- The bound on the derivatives of the slices, for positions in `closedBall p₀.1 1`.
  have hbound (ζ : E) (p : E × E) (hp : p.1 ∈ Metric.closedBall p₀.1 1) (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (F · ζ) p‖ ≤
        C * (1 + 2 * ‖(2 * π) • ζ‖) ^ i * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) := by
    set ξ := (2 * π) • ζ
    have he : ContDiff ℝ i fun p ↦ Complex.exp (kernelPhase ζ p) :=
      (kernelPhase ζ).contDiff.cexp
    have hg : ContDiff ℝ i fun y : E ↦ a (y, ξ) :=
      (ha.of_le (mod_cast hi)).comp (contDiff_id.prodMk contDiff_const)
    have hF' : (F · ζ) = fun p ↦ Complex.exp (kernelPhase ζ p) • a (p.1, ξ) := by
      rw [hF]
    -- The `j`-th derivative of the phase factor is at most `(2 ‖ξ‖) ^ j`.
    have he_le (j : ℕ) : ‖iteratedFDeriv ℝ j (fun p ↦ Complex.exp (kernelPhase ζ p)) p‖ ≤
        (2 * ‖ξ‖) ^ j := by
      refine ((kernelPhase ζ).norm_iteratedFDeriv_cexp_comp_le j p).trans ?_
      rw [exp_kernelPhase, Circle.norm_coe, one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_kernelPhase_le ζ) j
    -- The `r`-th derivative of the coefficient factor is at most `C ⟨ξ⟩ ^ m`.
    have hg_le (r : ℕ) (hr : r ≤ i) : ‖iteratedFDeriv ℝ r (fun p : E × E ↦ a (p.1, ξ)) p‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
      have hcomp := (ContinuousLinearMap.fst ℝ E E).iteratedFDeriv_comp_right hg p
        (i := r) (mod_cast hr)
      simp only [Function.comp_def, ContinuousLinearMap.coe_fst'] at hcomp
      rw [hcomp]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      refine (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
        (ContinuousLinearMap.norm_fst_le ℝ E E))).trans ?_
      exact hC r (hr.trans hi) p.1 hp ξ
    rw [hF']
    refine (norm_iteratedFDeriv_smul_le he (hg.comp contDiff_fst) p le_rfl).trans ?_
    calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (fun p ↦ Complex.exp (kernelPhase ζ p)) p‖ *
          ‖iteratedFDeriv ℝ (i - j) (fun p : E × E ↦ a (p.1, ξ)) p‖
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (2 * ‖ξ‖) ^ j *
          (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
          gcongr with j hj
          · exact he_le j
          · exact hg_le (i - j) (Nat.sub_le i j)
      _ = C * (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
          rw [← Finset.sum_mul, show 1 + 2 * ‖ξ‖ = 2 * ‖ξ‖ + 1 by ring, add_pow]
          simp only [one_pow, mul_one]
          rw [Finset.sum_congr rfl fun j _ ↦ mul_comm ((i.choose j : ℝ)) ((2 * ‖ξ‖) ^ j)]
          ring
  have hT := hasFTaylorSeriesUpToOn_integral_of_le_bound (μ := volume) (F := F)
    (s := Prod.fst ⁻¹' Metric.ball p₀.1 1) (n := (k : ℕ∞))
    (p := fun p ζ ↦ ftaylorSeries ℝ (F · ζ) p)
    (bound := fun i ζ ↦ C * (1 + 2 * ‖(2 * π) • ζ‖) ^ i * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2))
    hs (fun p _ i hi ↦ ?_) (ae_of_all _ fun ζ p hp i hi ↦ ?_) (fun i hi ↦ ?_)
    (ae_of_all _ fun ζ ↦ (contDiff_iff_ftaylorSeries.1 (hslice ζ)).hasFTaylorSeriesUpToOn _)
  · exact hT.contDiffOn.contDiffAt (hs.mem_nhds (Metric.mem_ball_self one_pos))
  · -- measurability: the derivatives of the slices are continuous in the frequency
    have hi' : i ≤ k := by exact_mod_cast hi
    -- Instance synthesis does not find the pseudo-metrizable structure of these multilinear maps
    -- on the product `E × E`, although their topology is the one of their norm.
    have : TopologicalSpace.PseudoMetrizableSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ E × E) (V →L[ℂ] W)) :=
      @PseudoEMetricSpace.pseudoMetrizableSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ E × E) (V →L[ℂ] W)) _
    simp only [ftaylorSeries, hslice_deriv _ i hi' p]
    exact ((ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp
      ((hΦ.continuous_iteratedFDeriv (mod_cast hi')).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · exact hbound ζ p (Metric.ball_subset_closedBall hp) i (by exact_mod_cast hi)
  · -- integrability: `(1 + 2 ‖ξ‖) ^ i ⟨ξ⟩ ^ m ≤ 3 ^ i ⟨ξ⟩ ^ (m + i)` with `m + i < -n`
    have hi' : (i : ℝ) ≤ k := by exact_mod_cast hi
    have hint := (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure E))
      (r := -(m + i)) (by linarith)).const_mul (|C| * 3 ^ i)
    refine (Integrable.mono' (f := fun ξ : E ↦ C * (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
      hint ?_ (ae_of_all _ fun ξ ↦ ?_)).comp_smul two_pi_pos.ne'
    · have hcont : Continuous fun ξ : E ↦ C * (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
        Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun ξ ↦
          Or.inl (by positivity))
      exact hcont.aestronglyMeasurable
    · have hw : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
      have hsqrt : 1 + 2 * ‖ξ‖ ≤ 3 * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        have h1 : 1 ≤ √(1 + ‖ξ‖ ^ 2) := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖ξ‖])
        have h2 : ‖ξ‖ ≤ √(1 + ‖ξ‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
        linarith
      have hpow : (1 + 2 * ‖ξ‖) ^ i ≤ 3 ^ i * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) := by
        rw [div_eq_mul_one_div (i : ℝ), mul_comm (i : ℝ), Real.rpow_mul hw.le, Real.rpow_natCast,
          ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hsqrt i
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity), neg_neg, mul_assoc, mul_assoc |C|]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
      calc (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2)
          ≤ 3 ^ i * (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by gcongr
        _ = 3 ^ i * (1 + ‖ξ‖ ^ 2) ^ ((m + i) / 2) := by
          rw [mul_assoc, ← Real.rpow_add hw]
          ring_nf

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


/-- **Smoothness of the kernel of a symbol.** The kernel of a symbol of order `m` is `C^k` as soon
as `m + k < -n`. -/
theorem contDiff_quantizationKernel (b : Symbol n V W m) (k : ℕ) (hk : m + k < -n) :
    ContDiff ℝ k (Function.uncurry (quantizationKernel b.coefficient)) := by
  refine contDiff_quantizationKernel_of_bound (b.contDiff_coefficient.of_le (mod_cast le_top))
    (by simpa using hk) fun K hK ↦ ?_
  choose C hC0 hC using fun α : List (Fin n) ↦ b.exists_bound K hK α []
  refine ⟨∑ i ∈ Finset.range (k + 1), ∑ r : Fin i → Fin n, C (List.ofFn r),
    fun i hi x hx ξ ↦ ?_⟩
  have hslice : ContDiff ℝ i fun y ↦ b.coefficient (y, ξ) :=
    (b.contDiff_coefficient_slice ξ).of_le (mod_cast le_top)
  refine (norm_iteratedFDeriv_le_sum_coordinateDeriv hslice x).trans ?_
  calc ∑ r : Fin i → Fin n, ‖coordinateDeriv (List.ofFn r) (fun y ↦ b.coefficient (y, ξ)) x‖
      ≤ ∑ r : Fin i → Fin n, C (List.ofFn r) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
        Finset.sum_le_sum fun r _ ↦ by simpa [mixedDeriv_def] using hC (List.ofFn r) x hx ξ
    _ = (∑ r : Fin i → Fin n, C (List.ofFn r)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ i ∈ Finset.range (k + 1), ∑ r : Fin i → Fin n, C (List.ofFn r)) *
        (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        gcongr
        exact Finset.single_le_sum (f := fun i ↦ ∑ r : Fin i → Fin n, C (List.ofFn r))
          (fun i _ ↦ Finset.sum_nonneg fun r _ ↦ hC0 _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-! ### The frequency Laplacian and multiplication by `‖x - y‖²` -/

/-- **Kernel of the frequency Laplacian.** For a symbol of order `m < -n`, the kernel of `Δ_ξ a` is
`-‖x - y‖² K_a(x, y)`. -/
theorem quantizationKernel_frequencyLaplacian (a : Symbol n V W m) (hm : m < -n)
    (x y : CoordinateSpace n) :
    quantizationKernel (frequencyLaplacian a).coefficient x y =
      (-‖x - y‖ ^ 2) • quantizationKernel a.coefficient x y := by
  rw [coefficient_frequencyLaplacian_eq_sum,
    quantizationKernel_sum _ fun j _ ↦ integrable_coefficient _ (by linarith) x]
  simp only [quantizationKernel_frequencyDeriv _ (by linarith : m - 1 < -n),
    quantizationKernel_frequencyDeriv _ hm, smul_smul, ← Finset.sum_smul]
  rw [← Complex.coe_smul, EuclideanSpace.real_norm_sq_eq]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination ((x - y) j : ℂ) ^ 2 * Complex.I_sq

/-- **Kernel of the iterated frequency Laplacian.** For a symbol of order `m < -n`, the kernel of
`Δ_ξ^N a` is `(-‖x - y‖²)^N K_a(x, y)`. -/
theorem quantizationKernel_iteratedFrequencyLaplacian (a : Symbol n V W m) (hm : m < -n) (N : ℕ)
    (x y : CoordinateSpace n) :
    quantizationKernel (iteratedFrequencyLaplacian N a).coefficient x y =
      (-‖x - y‖ ^ 2) ^ N • quantizationKernel a.coefficient x y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [coefficient_iteratedFrequencyLaplacian_succ,
      quantizationKernel_frequencyLaplacian _ (by linarith), ih, smul_smul, ← pow_succ']

end Symbol

end TauCeti
