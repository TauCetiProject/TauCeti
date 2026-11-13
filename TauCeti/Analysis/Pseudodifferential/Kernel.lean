/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
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
* `TauCeti.integral_fourierChar_smul_quantizationKernel`: the Fourier transform of an integrable
  kernel row `y ↦ K_a(x, y)` recovers the symbol `a(x, ·)`.
* `TauCeti.integral_quantizationKernel_comp_adjoint`: the kernel
  `∫ K_a(x, y) K_b(z, y)† dy = ∫ exp(2πi ⟪ζ, x - z⟫) a(x, 2πζ) b(z, 2πζ)† dζ` of `Op(a) Op(b)†`.
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
* `TauCeti.Symbol.IsSmoothing.contDiff_quantizationKernel`: the kernel of a smoothing symbol is
  `C^∞`.
* `TauCeti.Symbol.quantizationKernel_frequencyLaplacian` and
  `TauCeti.Symbol.quantizationKernel_frequencyLaplacianPow_add`: for `m < -n` the kernel of the
  frequency Laplacian `Δ_ξ a` is `-‖x - y‖² K_a(x, y)`, and iterating, the kernel of
  `Δ_ξ^(N + k) a` is `(-‖x - y‖²)^k K_{Δ_ξ^N a}(x, y)` once `m - 2N < -n`.
* `TauCeti.Symbol.quantizationKernel_mixedDeriv_replicate` and
  `TauCeti.Symbol.one_add_norm_div_pow_mul_norm_quantizationKernel_le`: iterating, the kernel of
  `∂_{ξ_j}^k a` is `(-i (x - y)_j)^k K_a(x, y)`, so the kernel decays off the diagonal at a rate
  controlled by the frequency integrals of the derivatives: if `∫ ‖a(x, ξ)‖ dξ ≤ A` and
  `∫ ‖∂_{ξ_j}^N a(x, ξ)‖ dξ ≤ A R^N` for every `j`, then
  `(1 + ‖x - y‖ / R)^N ‖K_a(x, y)‖ ≤ 2^N (1 + √n^N) (2π)⁻ⁿ A`.

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
  {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]

section NormedSpace

variable [NormedSpace ℂ V] [NormedSpace ℂ W]

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
  have hp : ‖p.1 - p.2‖ ≤ 2 * ‖p‖ := (norm_sub_le _ _).trans (by
    linarith [norm_fst_le p, norm_snd_le p])
  calc ‖kernelPhase ζ p‖ = 2 * π * |⟪ζ, p.1 - p.2⟫| := by
        simp [kernelPhase_apply, abs_of_pos pi_pos]
    _ ≤ 2 * π * (‖ζ‖ * ‖p.1 - p.2‖) := by gcongr; exact abs_real_inner_le_norm _ _
    _ ≤ 2 * π * (‖ζ‖ * (2 * ‖p‖)) := by gcongr
    _ = 2 * ‖(2 * π) • ζ‖ * ‖p‖ := by
        rw [norm_smul, Real.norm_of_nonneg two_pi_pos.le]
        ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Leibniz bound on the kernel integrand.** If the position derivatives of order at most `k` of
`a` satisfy `‖D_x^i a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` for `x ∈ s`, then the `i`-th derivative in `p = (x, y)`
of `exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ)` is at most `C (1 + 2 ‖2πζ‖) ^ i ⟨2πζ⟩ ^ m` for `x ∈ s`. -/
private theorem norm_iteratedFDeriv_kernelIntegrand_le {a : E × E → V →L[ℂ] W} {k : ℕ}
    {m C : ℝ} (ha : ContDiff ℝ k a) {s : Set E}
    (hC : ∀ i ≤ k, ∀ x ∈ s, ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun y ↦ a (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (ζ : E) {p : E × E} (hp : p.1 ∈ s) {i : ℕ} (hi : i ≤ k) :
    ‖iteratedFDeriv ℝ i (fun p ↦ Complex.exp (kernelPhase ζ p) • a (p.1, (2 * π) • ζ)) p‖ ≤
      C * (1 + 2 * ‖(2 * π) • ζ‖) ^ i * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) := by
  set ξ := (2 * π) • ζ
  have he : ContDiff ℝ i fun p ↦ Complex.exp (kernelPhase ζ p) :=
    (kernelPhase ζ).contDiff.cexp
  have hg : ContDiff ℝ i fun y : E ↦ a (y, ξ) :=
    (ha.of_le (mod_cast hi)).comp (contDiff_id.prodMk contDiff_const)
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
  refine (norm_iteratedFDeriv_smul_le he (hg.comp contDiff_fst) p le_rfl).trans ?_
  calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (fun p ↦ Complex.exp (kernelPhase ζ p)) p‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun p : E × E ↦ a (p.1, ξ)) p‖
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (2 * ‖ξ‖) ^ j *
        (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
        gcongr with j _
        · exact he_le j
        · exact hg_le (i - j) (Nat.sub_le i j)
    _ = C * (1 + 2 * ‖ξ‖) ^ i * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        rw [← Finset.sum_mul, show 1 + 2 * ‖ξ‖ = 2 * ‖ξ‖ + 1 by ring, add_pow]
        simp only [one_pow, mul_one]
        rw [Finset.sum_congr rfl fun j _ ↦ mul_comm ((i.choose j : ℝ)) ((2 * ‖ξ‖) ^ j)]
        ring

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
    simp only [ftaylorSeries, hΦ.contDiffAt.iteratedFDeriv_prod_left i (mod_cast hi')]
    exact ((ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp
      ((hΦ.continuous_iteratedFDeriv (mod_cast hi')).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · subst hF
    exact norm_iteratedFDeriv_kernelIntegrand_le ha (fun i hi ↦ hC i hi) ζ
      (Metric.ball_subset_closedBall hp) (by exact_mod_cast hi)
  · -- integrability: `(1 + 2 ‖ξ‖) ^ i ⟨ξ⟩ ^ m` is integrable since `m + i < -n`
    have hi' : (i : ℝ) ≤ k := by exact_mod_cast hi
    simpa only [neg_neg, mul_assoc] using
      ((integrable_one_add_mul_norm_pow_mul_rpow_neg_one_add_norm_sq (V := E) volume zero_le_two i
        (r := -m) (by linarith)).const_mul C).comp_smul two_pi_pos.ne'

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

/-- **The kernel determines the symbol.** If the frequency slice `ξ ↦ a(x, ξ)` is continuous and
integrable, and the kernel row `y ↦ K_a(x, y)` is integrable, then the Fourier transform of the
row recovers the symbol: `∫ exp(2πi ⟪ζ, y⟫) K_a(x, y) dy = exp(2πi ⟪ζ, x⟫) a(x, 2πζ)`. -/
theorem integral_fourierChar_smul_quantizationKernel [CompleteSpace W]
    (hc : Continuous fun ξ ↦ a (x, ξ)) (ha : Integrable fun ξ ↦ a (x, ξ))
    (hK : Integrable (quantizationKernel a x)) (ζ : E) :
    ∫ y, 𝐞 ⟪ζ, y⟫ • quantizationKernel a x y = 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) := by
  set A : E → V →L[ℂ] W := fun ζ ↦ a (x, (2 * π) • ζ)
  have hA : Integrable A := ha.comp_smul two_pi_pos.ne'
  have hAc : Continuous A := hc.comp (continuous_const_smul _)
  -- The kernel row is the inverse Fourier transform of `A`, reflected about `x`.
  have hrow (y : E) : quantizationKernel a x y = 𝓕⁻ A (x - y) :=
    quantizationKernel_eq_fourierInv a x y
  have hK' : Integrable (𝓕⁻ A) := by
    simpa [hrow] using hK.comp_sub_left x
  have hFA : Integrable (𝓕 A) := by
    simpa [fourierInv_eq_fourier_neg] using hK'.comp_neg
  calc ∫ y, 𝐞 ⟪ζ, y⟫ • quantizationKernel a x y
      = ∫ w, 𝐞 ⟪ζ, x - w⟫ • 𝓕⁻ A w := by
        rw [← integral_sub_left_eq_self _ (μ := volume) x]
        simp [hrow]
    _ = 𝐞 ⟪ζ, x⟫ • ∫ w, 𝐞 (-⟪w, ζ⟫) • 𝓕⁻ A w := by
        rw [Circle.smul_def, ← integral_smul]
        congr 1 with w
        simp only [Circle.smul_def]
        rw [fourierChar_inner_sub, mul_smul, real_inner_comm w ζ]
    _ = 𝐞 ⟪ζ, x⟫ • A ζ := by
        rw [← Real.fourier_eq, hA.fourier_fourierInv_eq hFA hAc.continuousAt]

namespace Symbol

/-! ### Kernels of symbols of order `m < -n` -/

variable {n : ℕ} {m : ℝ}

/-- The frequency slices of a symbol of order `m < -n` are integrable. -/
theorem integrable_coefficient (a : Symbol n V W m) (hm : m < -n) (x : CoordinateSpace n) :
    Integrable (fun ξ ↦ a.coefficient (x, ξ)) := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  have hweight := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (CoordinateSpace n)))
    (r := -m) (by simp only [finrank_euclideanSpace_fin]; linarith)
  refine (hweight.const_mul C).mono'
    (a.contDiff_coefficient.continuous.comp (continuous_const.prodMk continuous_id)
      ).aestronglyMeasurable (ae_of_all _ fun ξ ↦ ?_)
  simpa only [neg_neg] using hC ξ

/-- For symbols of order `m < -n`, the kernel is additive over finite sums. -/
theorem quantizationKernel_sum {ι : Type*} (s : Finset ι) (b : ι → Symbol n V W m)
    (hm : m < -n) (x y : CoordinateSpace n) :
    quantizationKernel (∑ i ∈ s, b i).coefficient x y =
      ∑ i ∈ s, quantizationKernel (b i).coefficient x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coefficient_add,
      quantizationKernel_add ((b i).integrable_coefficient hm x)
        ((∑ i ∈ s, b i).integrable_coefficient hm x), ih]

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
  have h := inner_smul_quantizationKernel (a.hasLineDerivAt_coefficient_single j x)
    (a.integrable_coefficient hm x)
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

/-- **The kernel of a smoothing symbol is smooth.** A smoothing symbol has a coefficient of every
order, so its kernel is `C^k` for every `k` by `TauCeti.Symbol.contDiff_quantizationKernel`. -/
theorem IsSmoothing.contDiff_quantizationKernel {a : Symbol n V W m} (ha : a.IsSmoothing) :
    ContDiff ℝ ∞ (Function.uncurry (quantizationKernel a.coefficient)) :=
  contDiff_infty.2 fun k ↦ by
    obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha (-n - k - 1)
    rw [← hb]
    exact b.contDiff_quantizationKernel k (by linarith)

/-! ### The frequency Laplacian and multiplication by `‖x - y‖²` -/

/-- **Kernel of the frequency Laplacian.** For a symbol of order `m < -n`,
`K_{Δ_ξ a}(x, y) = -‖x - y‖² K_a(x, y)`. -/
theorem quantizationKernel_frequencyLaplacian (a : Symbol n V W m) (hm : m < -n)
    (x y : CoordinateSpace n) :
    quantizationKernel (frequencyLaplacian a).coefficient x y =
      (-‖x - y‖ ^ 2) • quantizationKernel a.coefficient x y := by
  rw [frequencyLaplacian_eq_sum, quantizationKernel_sum _ _ (by linarith)]
  simp only [coefficient_inclusion]
  simp_rw [quantizationKernel_frequencyDeriv _ (by linarith : m - 1 < -n),
    quantizationKernel_frequencyDeriv _ hm, smul_smul, ← Finset.sum_smul]
  rw [← Complex.coe_smul]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination (((x - y) j : ℂ)) ^ 2 * Complex.I_sq

/-- Iterating `TauCeti.Symbol.quantizationKernel_frequencyLaplacian`: once `m - 2N < -n`,
`K_{Δ_ξ^(N + k) a}(x, y) = (-‖x - y‖²)^k K_{Δ_ξ^N a}(x, y)`. -/
theorem quantizationKernel_frequencyLaplacianPow_add (a : Symbol n V W m) {N : ℕ}
    (hN : m - 2 * N < -n) (k : ℕ) (x y : CoordinateSpace n) :
    quantizationKernel (frequencyLaplacianPow (N + k) a).coefficient x y =
      (-‖x - y‖ ^ 2) ^ k • quantizationKernel (frequencyLaplacianPow N a).coefficient x y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, coefficient_frequencyLaplacianPow_succ',
      quantizationKernel_frequencyLaplacian _ (by push_cast; linarith), ih, smul_smul,
      pow_succ (-‖x - y‖ ^ 2) k, mul_comm]

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

end Symbol

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℂ V] [CompleteSpace V] [InnerProductSpace ℂ W] [CompleteSpace W]

open ContinuousLinearMap in
/-- **The kernel of `Op(b)†`.** The adjoint `K_b(z, y)†` of the kernel of `b` is
`∫ exp(2πi ⟪ζ, y - z⟫) b(z, 2πζ)† dζ`, whenever the frequency slice `ξ ↦ b(z, ξ)` is
integrable. -/
theorem adjoint_quantizationKernel {b : E × E → V →L[ℂ] W} {z : E}
    (hb : Integrable fun ξ ↦ b (z, ξ)) (y : E) :
    adjoint (quantizationKernel b z y) = ∫ ζ, 𝐞 ⟪ζ, y - z⟫ • adjoint (b (z, (2 * π) • ζ)) := by
  have hb' : Integrable fun ζ ↦ 𝐞 ⟪ζ, z - y⟫ • b (z, (2 * π) • ζ) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-(z - y))).2 (hb.comp_smul two_pi_pos.ne')
  have h := integral_comp_commSL (X := E) (μ := volume) (σ := starRingEnd ℂ) (by simp)
    ((adjoint : (V →L[ℂ] W) ≃ₗᵢ⋆[ℂ] (W →L[ℂ] V)).toContinuousLinearEquiv :
      (V →L[ℂ] W) →SL[starRingEnd ℂ] (W →L[ℂ] V)) hb'
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h
  rw [quantizationKernel_def, ← h]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  simp only [Circle.smul_def, map_smulₛₗ, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv,
    ← inner_neg_right, neg_sub]

open ContinuousLinearMap in
/-- **The kernel of `Op(a) Op(b)†`.** The kernel `∫ K_a(x, y) K_b(z, y)† dy` of `Op(a) Op(b)†` is
`∫ exp(2πi ⟪ζ, x - z⟫) a(x, 2πζ) b(z, 2πζ)† dζ`, whenever the frequency slices `ξ ↦ a(x, ξ)` and
`ξ ↦ b(z, ξ)` are integrable, the first one continuous, and the kernel row `y ↦ K_a(x, y)` is
integrable. -/
theorem integral_quantizationKernel_comp_adjoint {a b : E × E → V →L[ℂ] W} {x z : E}
    (hac : Continuous fun ξ ↦ a (x, ξ)) (ha : Integrable fun ξ ↦ a (x, ξ))
    (hK : Integrable (quantizationKernel a x)) (hb : Integrable fun ξ ↦ b (z, ξ)) :
    ∫ y, quantizationKernel a x y ∘L adjoint (quantizationKernel b z y) =
      ∫ ζ, 𝐞 ⟪ζ, x - z⟫ • (a (x, (2 * π) • ζ) ∘L adjoint (b (z, (2 * π) • ζ))) := by
  set A : E → V →L[ℂ] W := fun ζ ↦ a (x, (2 * π) • ζ)
  set B : E → W →L[ℂ] V := fun ζ ↦ adjoint (b (z, (2 * π) • ζ))
  set K : E → V →L[ℂ] W := quantizationKernel a x
  -- Multiplying by a character preserves integrability.
  have hchar {X : Type _} [NormedAddCommGroup X] [NormedSpace ℂ X] {g : E → X}
      (hg : Integrable g) (w : E) : Integrable fun ζ ↦ 𝐞 ⟪ζ, w⟫ • g ζ := by
    simpa only [inner_neg_right, neg_neg] using (Real.fourierIntegral_convergent_iff (-w)).2 hg
  have hb' : Integrable fun ζ ↦ b (z, (2 * π) • ζ) := hb.comp_smul two_pi_pos.ne'
  have hB : Integrable B :=
    (LinearIsometryEquiv.integrable_comp_iff (adjoint : (V →L[ℂ] W) ≃ₗᵢ⋆[ℂ] (W →L[ℂ] V))).2 hb'
  -- Fubini's theorem applies to `(y, ζ) ↦ exp(2πi ⟪ζ, y - z⟫) K(y) B(ζ)`, dominated by
  -- `‖K(y)‖ ‖B(ζ)‖`.
  have hKc : Continuous K := continuous_quantizationKernel_right ha
  have hF : Integrable (Function.uncurry fun y ζ ↦ 𝐞 ⟪ζ, y - z⟫ • (K y ∘L B ζ))
      (volume.prod volume) := by
    refine (hK.norm.mul_prod hB.norm).mono' ?_ (.of_forall fun p ↦ ?_)
    · have h₁ : AEStronglyMeasurable (fun p : E × E ↦ K p.1 ∘L B p.2) (volume.prod volume) :=
        (compL ℂ W V W).aestronglyMeasurable_comp₂ hKc.aestronglyMeasurable.comp_fst
          hB.aestronglyMeasurable.comp_snd
      have h₂ : Continuous fun p : E × E ↦ ((𝐞 ⟪p.2, p.1 - z⟫ : Circle) : ℂ) := by fun_prop
      refine (h₂.aestronglyMeasurable.smul h₁).congr (.of_forall fun ⟨y, ζ⟩ ↦ ?_)
      rw [Function.uncurry_apply_pair, Circle.smul_def, Pi.smul_apply']
    · obtain ⟨y, ζ⟩ := p
      rw [Function.uncurry_apply_pair, Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
      exact opNorm_comp_le _ _
  calc ∫ y, K y ∘L adjoint (quantizationKernel b z y)
      = ∫ y, ∫ ζ, 𝐞 ⟪ζ, y - z⟫ • (K y ∘L B ζ) := by
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        dsimp only
        have h := (compL ℂ W V W (K y)).integral_comp_comm (hchar hB (y - z))
        simp only [compL_apply] at h
        rw [adjoint_quantizationKernel hb y, ← h]
        simp only [Circle.smul_def, comp_smul]
    _ = ∫ ζ, ∫ y, 𝐞 ⟪ζ, y - z⟫ • (K y ∘L B ζ) := integral_integral_swap hF
    _ = ∫ ζ, 𝐞 ⟪ζ, x - z⟫ • (A ζ ∘L B ζ) := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        dsimp only
        have h (y : E) : 𝐞 ⟪ζ, y - z⟫ • (K y ∘L B ζ) =
            (𝐞 (-⟪ζ, z⟫) : ℂ) • (compL ℂ W V W).flip (B ζ) ((𝐞 ⟪ζ, y⟫ : ℂ) • K y) := by
          rw [map_smul, smul_smul, Circle.smul_def, fourierChar_inner_sub, mul_comm, flip_apply,
            compL_apply]
        have hint : Integrable fun y ↦ (𝐞 ⟪ζ, y⟫ : ℂ) • K y := by
          simpa only [Circle.smul_def, real_inner_comm] using hchar hK ζ
        have hrow := integral_fourierChar_smul_quantizationKernel hac ha hK ζ
        simp only [Circle.smul_def] at hrow
        simp_rw [h, integral_smul]
        rw [(compL ℂ W V W).flip (B ζ) |>.integral_comp_comm hint, hrow, flip_apply, compL_apply,
          smul_comp, smul_smul, Circle.smul_def, fourierChar_inner_sub, mul_comm]

end InnerProductSpace

end TauCeti
