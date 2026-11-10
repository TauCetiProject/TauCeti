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

end Symbol

end TauCeti
