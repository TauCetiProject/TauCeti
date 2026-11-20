/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The left symbol of a right quantization

The right quantization of a coefficient `c(y, ξ)` depending on the input variable `y` is
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ`. Formal adjoints of left (Kohn–Nirenberg)
quantizations are of this form, so to stay in the calculus one rewrites a right quantization as a
left one. For a symbol `c` of order `m` with compact spatial support this file constructs the left
symbol

`b(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) dθ`,

where `ĉ(θ, ξ)` is Mathlib's Fourier transform of the position slice `z ↦ c(z, ξ)`, and proves
that it is a symbol of order `m` whose quantization is the right quantization of `c`.

## Main declarations

* `TauCeti.Symbol.ofRight`: the left symbol `b` of the right quantization of `c`, a symbol of
  order `m` with estimates uniform in the position (`TauCeti.Symbol.isUniform_ofRight`), whose
  position and frequency derivatives are the left symbols of the derivatives of `c`
  (`TauCeti.Symbol.spatialDeriv_ofRight`, `TauCeti.Symbol.frequencyDeriv_ofRight`).
* `TauCeti.Symbol.quantizeSchwartzValue_ofRight`: `Op(b) v (x)` is the right quantization
  `∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ c(y, 2πζ) v(y)) (ζ) dζ` of `c`; as operators on Schwartz space,
  `TauCeti.Symbol.quantizeRightUniformCLM_eq_quantizeUniformCLM_ofRight`.
* `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_fourier_slice_add_smul_le`,
  `TauCeti.Symbol.HasCompactSpatialSupport.integrable_fourierChar_smul_fourier_slice_add_smul`:
  the decay `‖ĉ(θ, ξ + sθ)‖ ≤ C ⟨ξ⟩ ^ m (1 + ‖θ‖) ^ (-(n + 1))` of the shifted Fourier slices and
  the resulting integrability of `exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + sθ)` in `θ`, for every real `s`.

## The estimates

Since `c` has compact spatial support, `ĉ(θ, ξ)` decays faster than every power of `θ`, with
`‖ĉ(θ, ξ)‖ ≤ C_N (1 + ‖θ‖) ^ (-N) ⟨ξ⟩ ^ m`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`). Peetre's
inequality `⟨ξ + 2πθ⟩ ^ m ≤ 2 ^ (|m| / 2) ⟨ξ⟩ ^ m ⟨2πθ⟩ ^ |m|` then bounds the integrand of `b`
by `C ⟨ξ⟩ ^ m (1 + ‖θ‖) ^ (-(n + 1))`, which is integrable in `θ`. The derivative `2πi θⱼ` of the
phase in `x_j` is the Fourier multiplier of `∂_{x_j} c`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_spatialDeriv_slice`), and `ĉ` is differentiated
in `ξ` under the position integral
(`TauCeti.Symbol.HasCompactSpatialSupport.coordinateDeriv_fourier_slice`). So every derivative of
the integrand, and after differentiating under the integral sign every derivative of `b`, is the
left symbol of the corresponding derivative of `c`, and the estimates of all mixed derivatives
follow from the bound above by induction.

## Implementation notes

Integrals of the derivatives are linear maps on `ℝⁿ × ℝⁿ` with values in `V →L[ℂ] W`. On this
concrete space the `PseudoMetrizableSpace` instance search behind `AEStronglyMeasurable` exceeds
the typeclass heartbeat limit, so the lemmas that need it are stated for an abstract complex normed
space `F` and only then applied to `F = V →L[ℂ] W`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Module
open scoped RealInnerProductSpace SchwartzMap ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The integrand and its decay -/

section Right

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- The integrand `exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ)` of the left symbol of the right quantization of
`c`, where `ĉ(θ, ξ)` is the Fourier transform of the position slice `z ↦ c(z, ξ)`. -/
private def rightIntegrand (c : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n) : V →L[ℂ] W :=
  (𝐞 ⟪θ, p.1⟫ : ℂ) • 𝓕 (fun z ↦ c (z, p.2 + (2 * π) • θ)) θ

/-- The left symbol `∫ exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) dθ` of the right quantization of `c`. -/
private def rightCoeff (c : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  ∫ θ, rightIntegrand c p θ

variable {c : Symbol n V W m}

/-- The Fourier transform `ĉ(θ, ξ)` of the position slices of a symbol with compact spatial support
decays faster than `(1 + ‖θ‖) ^ (-(n + 1 + |m|))`. -/
private theorem HasCompactSpatialSupport.exists_norm_fourier_le (hc : c.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ θ ξ : CoordinateSpace n, ‖𝓕 (fun z ↦ c.coefficient (z, ξ)) θ‖ ≤
      C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_one_add_norm_pow_mul_norm_fourier_le (n + 1 + ⌈|m|⌉₊)
  refine ⟨C, hC0, fun θ ξ ↦ ?_⟩
  have h1 : 1 ≤ 1 + ‖θ‖ := le_add_of_nonneg_right (norm_nonneg θ)
  have hexp : (n : ℝ) + 1 + |m| ≤ ((n + 1 + ⌈|m|⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil |m|]
  have hle : 1 ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖θ‖) ^ (n + 1 + ⌈|m|⌉₊) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
    exact Real.one_le_rpow h1 (by linarith)
  calc ‖𝓕 (fun z ↦ c.coefficient (z, ξ)) θ‖
      ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖θ‖) ^ (n + 1 + ⌈|m|⌉₊) *
          ‖𝓕 (fun z ↦ c.coefficient (z, ξ)) θ‖ := le_mul_of_one_le_left (norm_nonneg _) hle
    _ = (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) *
          ((1 + ‖θ‖) ^ (n + 1 + ⌈|m|⌉₊) * ‖𝓕 (fun z ↦ c.coefficient (z, ξ)) θ‖) := by ring
    _ ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
        mul_le_mul_of_nonneg_left (hC θ ξ) (by positivity)
    _ = C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring

/-- The weight `⟨θ⟩ ^ |m|` lost to Peetre's inequality is absorbed by the decay of `ĉ`. -/
private theorem weight_mul_decay_le (θ : CoordinateSpace n) :
    (1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) ≤
      (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  have hsplit : (1 + ‖θ‖) ^ |m| * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) =
      (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  rw [← hsplit]
  gcongr
  exact one_add_norm_sq_rpow_le_one_add_norm_rpow θ (abs_nonneg m)

/-- **Decay of the shifted Fourier slices.** For a symbol `c` of order `m` with compact spatial
support and a real `s`, `‖ĉ(θ, ξ + sθ)‖ ≤ C ⟨ξ⟩ ^ m (1 + ‖θ‖) ^ (-(n + 1))`: the decay of `ĉ` in
its first variable absorbs the growth `⟨sθ⟩ ^ |m|` of Peetre's inequality in the shift. -/
theorem HasCompactSpatialSupport.exists_norm_fourier_slice_add_smul_le
    (hc : c.HasCompactSpatialSupport) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ θ ξ : CoordinateSpace n, ‖𝓕 (fun z ↦ c.coefficient (z, ξ + s • θ)) θ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_fourier_le
  have hr : 1 ≤ max |s| 1 := le_max_right _ _
  refine ⟨C * 2 ^ (|m| / 2) * max |s| 1 ^ |m|, by positivity, fun θ ξ ↦ ?_⟩
  -- The bracket of the shift is at most `max |s| 1 ^ |m| ⟨θ⟩ ^ |m|`.
  have hshift : (1 + ‖s • θ‖ ^ 2) ^ (|m| / 2) ≤ max |s| 1 ^ |m| * (1 + ‖θ‖ ^ 2) ^ (|m| / 2) := by
    have h := one_add_norm_smul_sq_rpow_le hr |m| θ
    rw [abs_abs] at h
    refine le_trans ?_ h
    gcongr
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (zero_le_one.trans hr)]
    gcongr
    exact le_max_left _ _
  calc ‖𝓕 (fun z ↦ c.coefficient (z, ξ + s • θ)) θ‖
      ≤ C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖ξ + s • θ‖ ^ 2) ^ (m / 2) := hC θ _
    _ ≤ C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          (max |s| 1 ^ |m| * (1 + ‖θ‖ ^ 2) ^ (|m| / 2))) := by
        gcongr
        exact (one_add_norm_add_sq_rpow_le_mul m ξ (s • θ)).trans (by gcongr)
    _ = C * 2 ^ (|m| / 2) * max |s| 1 ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|))) := by ring
    _ ≤ C * 2 ^ (|m| / 2) * max |s| 1 ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
        gcongr
        exact weight_mul_decay_le θ

/-- The shifted integrand `exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + sθ)` is integrable in `θ`, for every real
`s`. -/
theorem HasCompactSpatialSupport.integrable_fourierChar_smul_fourier_slice_add_smul
    (hc : c.HasCompactSpatialSupport) (s : ℝ) (x ξ : CoordinateSpace n) :
    Integrable fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun z ↦ c.coefficient (z, ξ + s • θ)) θ := by
  obtain ⟨C, -, hC⟩ := hc.exists_norm_fourier_slice_add_smul_le s
  have h₂ := hc.continuous_fourier_slice.comp (by fun_prop : Continuous
    fun θ : CoordinateSpace n ↦ ((θ, ξ + s • θ) : CoordinateSpace n × CoordinateSpace n))
  simp only [Function.comp_def] at h₂
  exact (integrable_one_add_norm_rpow_neg_add_one.const_mul (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))).mono'
    ((by fun_prop : Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, x⟫ : ℂ)).smul
      h₂).aestronglyMeasurable
    (.of_forall fun θ ↦ by rw [norm_smul, Circle.norm_coe, one_mul]; exact hC θ ξ)

/-- **The integrand decays in `θ`.**
`‖exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ)‖ ≤ C ⟨ξ⟩ ^ m (1 + ‖θ‖) ^ (-(n + 1))`, uniformly in the position
`x`. -/
private theorem HasCompactSpatialSupport.exists_norm_rightIntegrand_le
    (hc : c.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ p θ, ‖rightIntegrand c.coefficient p θ‖ ≤
      C * (1 + ‖p.2‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_fourier_slice_add_smul_le (2 * π)
  refine ⟨C, hC0, fun p θ ↦ ?_⟩
  rw [rightIntegrand, norm_smul, Circle.norm_coe, one_mul]
  exact hC θ p.2

/-- The integrand is jointly continuous in the point and the frequency `θ`. -/
private theorem HasCompactSpatialSupport.continuous_rightIntegrand
    (hc : c.HasCompactSpatialSupport) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      rightIntegrand c.coefficient q.1 q.2 := by
  have h₁ : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      (𝐞 ⟪q.2, q.1.1⟫ : ℂ) := by fun_prop
  have hg : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      ((q.2, q.1.2 + (2 * π) • q.2) : CoordinateSpace n × CoordinateSpace n) := by fun_prop
  have h₂ := hc.continuous_fourier_slice.comp hg
  simp only [Function.comp_def] at h₂
  exact h₁.smul h₂

/-- The integrand is integrable in `θ`. -/
private theorem HasCompactSpatialSupport.integrable_rightIntegrand
    (hc : c.HasCompactSpatialSupport) (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable (rightIntegrand c.coefficient p) :=
  hc.integrable_fourierChar_smul_fourier_slice_add_smul (2 * π) p.1 p.2

/-- **The symbol bound.** `‖∫ exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) dθ‖ ≤ C ⟨ξ⟩ ^ m`, uniformly in `x`. -/
private theorem HasCompactSpatialSupport.exists_norm_rightCoeff_le
    (hc : c.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ p, ‖rightCoeff c.coefficient p‖ ≤ C * (1 + ‖p.2‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_rightIntegrand_le
  refine ⟨C * ∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1)), by positivity, fun p ↦ ?_⟩
  calc ‖rightCoeff c.coefficient p‖
      ≤ ∫ θ, C * (1 + ‖p.2‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) :=
        norm_integral_le_of_norm_le (integrable_one_add_norm_rpow_neg_add_one.const_mul _)
          (.of_forall (hC p))
    _ = C * (∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1))) *
          (1 + ‖p.2‖ ^ 2) ^ (m / 2) := by
        rw [integral_const_mul]
        ring

end Right

/-! ### Measurability of the derivatives -/

section Measurability

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A continuous family of linear maps is a.e. strongly measurable.

This instance of `Continuous.aestronglyMeasurable` is stated over an abstract codomain `F`:
applied directly to the concrete codomain `_ →L[ℝ] V →L[ℂ] W` below, the search for its
`PseudoMetrizableSpace` instance exceeds the default typeclass heartbeat limit. -/
private theorem aestronglyMeasurable_of_continuous_clm {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {φ : CoordinateSpace n → H →L[ℝ] F} (hφ : Continuous φ) :
    AEStronglyMeasurable φ :=
  hφ.aestronglyMeasurable

end Measurability

/-! ### Smoothness of the left symbol -/

section Smooth

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {c : Symbol n V W m}

/-- The derivative in the point `p` of the integrand. -/
private def rightDeriv (c : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n)
    (θ : CoordinateSpace n) : CoordinateSpace n × CoordinateSpace n →L[ℝ] V →L[ℂ] W :=
  fderiv ℝ (fun p ↦ rightIntegrand c.coefficient p θ) p

/-- The integrand is differentiable in the point `(x, ξ)`: the phase `exp(2πi ⟪θ, x⟫)` is smooth,
and the Fourier slice `ĉ(θ, ξ + 2πθ)` is differentiable in `ξ`. -/
private theorem HasCompactSpatialSupport.differentiableAt_rightIntegrand
    (hc : c.HasCompactSpatialSupport) (θ : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ rightIntegrand c.coefficient p θ) p := by
  have he₀ := (Real.hasDerivAt_fourierChar ⟪θ, p.1⟫).hasFDerivAt.comp p
    (((innerSL ℝ θ).hasFDerivAt).comp p hasFDerivAt_fst)
  have he : HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 ⟪θ, p.1⟫ : ℂ)) _ p :=
    he₀
  have hF : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun z ↦ c.coefficient (z, p.2 + (2 * π) • θ)) θ) p :=
    (hc.hasFDerivAt_fourier_slice θ _).differentiableAt.comp p
      (differentiableAt_snd.add_const _)
  exact he.differentiableAt.smul hF

/-- A position derivative of the integrand is the integrand of the position derivative: the
derivative `2πi θⱼ` of the phase is the Fourier multiplier of `∂_{x_j}`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_spatialDeriv_slice`). -/
private theorem HasCompactSpatialSupport.coordinateDeriv_fst_rightIntegrand
    (hc : c.HasCompactSpatialSupport) (j : Fin n) (x ξ θ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ rightIntegrand c.coefficient (x, ξ) θ) x =
      rightIntegrand (Symbol.spatialDeriv j c).coefficient (x, ξ) θ := by
  set F := 𝓕 (fun z ↦ c.coefficient (z, ξ + (2 * π) • θ)) θ
  have he := (Real.hasDerivAt_fourierChar ⟪θ, x⟫).hasFDerivAt.comp x
    ((innerSL ℝ θ).hasFDerivAt (x := x))
  have h : HasFDerivAt (fun x ↦ (𝐞 ⟪θ, x⟫ : ℂ) • F) _ x := he.smul_const F
  simp only [rightIntegrand]
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv, hc.fourier_spatialDeriv_slice]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_smul, Complex.real_smul]
  congr 1
  ring

/-- A frequency derivative of the integrand is the integrand of the frequency derivative
(`TauCeti.Symbol.HasCompactSpatialSupport.coordinateDeriv_fourier_slice`). -/
private theorem HasCompactSpatialSupport.coordinateDeriv_snd_rightIntegrand
    (hc : c.HasCompactSpatialSupport) (j : Fin n) (x ξ θ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ rightIntegrand c.coefficient (x, ξ) θ) ξ =
      rightIntegrand (Symbol.frequencyDeriv j c).coefficient (x, ξ) θ := by
  have hF := hc.hasFDerivAt_fourier_slice θ (ξ + (2 * π) • θ)
  have h : HasFDerivAt
      (fun ξ ↦ (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun z ↦ c.coefficient (z, ξ + (2 * π) • θ)) θ) _ ξ :=
    (hF.comp ξ ((hasFDerivAt_id ξ).add_const ((2 * π) • θ))).const_smul (𝐞 ⟪θ, x⟫ : ℂ)
  simp only [rightIntegrand]
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv, ← hc.coordinateDeriv_fourier_slice,
    coordinateDeriv_cons, coordinateDeriv_nil, hF.fderiv]
  simp

/-- The derivative of the integrand in the direction `v`, through the integrands of the first-order
derivatives of the symbol. -/
private theorem HasCompactSpatialSupport.rightDeriv_apply (hc : c.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n)
    (v : CoordinateSpace n × CoordinateSpace n) :
    rightDeriv c p θ v = ∑ j, v.1 j • rightIntegrand (Symbol.spatialDeriv j c).coefficient p θ +
      ∑ j, v.2 j • rightIntegrand (Symbol.frequencyDeriv j c).coefficient p θ := by
  rw [rightDeriv, fderiv_apply_eq_sum_coordinateDeriv (hc.differentiableAt_rightIntegrand θ p)]
  simp only [hc.coordinateDeriv_fst_rightIntegrand, hc.coordinateDeriv_snd_rightIntegrand]

/-- Near a point `p₀`, the integrand is bounded by a multiple of `(1 + ‖θ‖) ^ (-(n + 1))`. -/
private theorem HasCompactSpatialSupport.exists_norm_rightIntegrand_le_of_mem_ball
    (hc : c.HasCompactSpatialSupport) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ B, 0 ≤ B ∧ ∀ p ∈ Metric.ball p₀ 1, ∀ θ,
      ‖rightIntegrand c.coefficient p θ‖ ≤ B * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_rightIntegrand_le
  have hcont : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
      (1 + ‖p.2‖ ^ 2) ^ (m / 2) :=
    (by fun_prop : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
      1 + ‖p.2‖ ^ 2).rpow_const fun _ ↦ Or.inl (by positivity)
  obtain ⟨D, hD⟩ := (isCompact_closedBall p₀ 1).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C * max D 0, by positivity, fun p hp θ ↦ (hC p θ).trans ?_⟩
  have hDp : (1 + ‖p.2‖ ^ 2) ^ (m / 2) ≤ max D 0 := by
    have h := hD p (Metric.ball_subset_closedBall hp)
    rw [Real.norm_of_nonneg (by positivity)] at h
    exact h.trans (le_max_left _ _)
  gcongr

/-- Near a point `p₀`, the derivative of the integrand is bounded by a multiple of
`(1 + ‖θ‖) ^ (-(n + 1))`. -/
private theorem HasCompactSpatialSupport.exists_norm_rightDeriv_le
    (hc : c.HasCompactSpatialSupport) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ B, 0 ≤ B ∧ ∀ p ∈ Metric.ball p₀ 1, ∀ θ,
      ‖rightDeriv c p θ‖ ≤ B * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  choose Bx hBx0 hBx using fun j ↦ (hc.spatialDeriv j).exists_norm_rightIntegrand_le_of_mem_ball p₀
  choose Bξ hBξ0 hBξ using fun j ↦
    (hc.frequencyDeriv j).exists_norm_rightIntegrand_le_of_mem_ball p₀
  refine ⟨∑ j, Bx j + ∑ j, Bξ j, add_nonneg (Finset.sum_nonneg fun j _ ↦ hBx0 j)
    (Finset.sum_nonneg fun j _ ↦ hBξ0 j), fun p hp θ ↦ ?_⟩
  refine ((rightDeriv c p θ).opNorm_le_of_apply_eq_sum _ _ (hc.rightDeriv_apply p θ)).trans ?_
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  gcongr with j _ j _
  · exact hBx j p hp θ
  · exact hBξ j p hp θ

/-- The derivative of the integrand is continuous in `θ`. -/
private theorem HasCompactSpatialSupport.continuous_rightDeriv (hc : c.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) : Continuous (rightDeriv c p) := by
  refine continuous_clm_apply.2 fun v ↦ ?_
  simp_rw [hc.rightDeriv_apply]
  refine (continuous_finsetSum _ fun j _ ↦ ?_).add (continuous_finsetSum _ fun j _ ↦ ?_)
  · exact ((hc.spatialDeriv j).continuous_rightIntegrand.comp
      (by fun_prop : Continuous fun θ : CoordinateSpace n ↦ (p, θ))).const_smul (v.1 j)
  · exact ((hc.frequencyDeriv j).continuous_rightIntegrand.comp
      (by fun_prop : Continuous fun θ : CoordinateSpace n ↦ (p, θ))).const_smul (v.2 j)

/-- **Differentiation under the frequency integral.** -/
private theorem HasCompactSpatialSupport.hasFDerivAt_rightCoeff (hc : c.HasCompactSpatialSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (rightCoeff c.coefficient) (∫ θ, rightDeriv c p₀ θ) p₀ := by
  obtain ⟨B, -, hB⟩ := hc.exists_norm_rightDeriv_le p₀
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ one_pos)
    (.of_forall fun p ↦ (hc.integrable_rightIntegrand p).aestronglyMeasurable)
    (hc.integrable_rightIntegrand p₀) (aestronglyMeasurable_of_continuous_clm
      (hc.continuous_rightDeriv p₀))
    (.of_forall fun θ p hp ↦ hB p hp θ) (integrable_one_add_norm_rpow_neg_add_one.const_mul B)
    (.of_forall fun θ p _ ↦ (hc.differentiableAt_rightIntegrand θ p).hasFDerivAt)

/-- The derivative of the left symbol in the direction `v`, through the left symbols of the
first-order derivatives of `c`. -/
private theorem HasCompactSpatialSupport.fderiv_rightCoeff_apply (hc : c.HasCompactSpatialSupport)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (rightCoeff c.coefficient) p v =
      ∑ j, v.1 j • rightCoeff (Symbol.spatialDeriv j c).coefficient p +
        ∑ j, v.2 j • rightCoeff (Symbol.frequencyDeriv j c).coefficient p := by
  have hx (j : Fin n) : Integrable fun θ ↦
      v.1 j • rightIntegrand (Symbol.spatialDeriv j c).coefficient p θ :=
    ((hc.spatialDeriv j).integrable_rightIntegrand p).smul (v.1 j)
  have hξ (j : Fin n) : Integrable fun θ ↦
      v.2 j • rightIntegrand (Symbol.frequencyDeriv j c).coefficient p θ :=
    ((hc.frequencyDeriv j).integrable_rightIntegrand p).smul (v.2 j)
  obtain ⟨B, -, hB⟩ := hc.exists_norm_rightDeriv_le p
  rw [(hc.hasFDerivAt_rightCoeff p).fderiv, ContinuousLinearMap.integral_apply
    ((integrable_one_add_norm_rpow_neg_add_one.const_mul B).mono'
      (aestronglyMeasurable_of_continuous_clm (hc.continuous_rightDeriv p))
      (.of_forall (hB p (Metric.mem_ball_self one_pos)))) v]
  simp_rw [hc.rightDeriv_apply]
  rw [integral_add (integrable_finsetSum _ fun j _ ↦ hx j) (integrable_finsetSum _ fun j _ ↦ hξ j),
    integral_finsetSum _ fun j _ ↦ hx j, integral_finsetSum _ fun j _ ↦ hξ j]
  simp_rw [integral_smul, rightCoeff]

/-- The left symbol is `C^k` for every `k`. -/
private theorem HasCompactSpatialSupport.contDiff_rightCoeff (k : ℕ) :
    ∀ {m : ℝ} {c : Symbol n V W m}, c.HasCompactSpatialSupport →
      ContDiff ℝ k (rightCoeff c.coefficient) := by
  induction k with
  | zero =>
    intro m c hc
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun p ↦
      (hc.hasFDerivAt_rightCoeff p).continuousAt)
  | succ k ih =>
    intro m c hc
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv_apply.2 ⟨fun p ↦ (hc.hasFDerivAt_rightCoeff p).differentiableAt,
      by simp, fun v ↦ ?_⟩
    simp_rw [hc.fderiv_rightCoeff_apply]
    exact (ContDiff.sum fun j _ ↦ (ih (hc.spatialDeriv j)).const_smul _).add
      (ContDiff.sum fun j _ ↦ (ih (hc.frequencyDeriv j)).const_smul _)

/-- A frequency derivative of the left symbol is the left symbol of the frequency derivative. -/
private theorem HasCompactSpatialSupport.coordinateDeriv_snd_rightCoeff
    (hc : c.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun η ↦ rightCoeff c.coefficient (x, η)) ξ =
      rightCoeff (Symbol.frequencyDeriv j c).coefficient (x, ξ) := by
  have h := (hc.hasFDerivAt_rightCoeff (x, ξ)).differentiableAt.hasFDerivAt.comp ξ
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x ξ)
  rw [Function.comp_def] at h
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    hc.fderiv_rightCoeff_apply, PiLp.zero_apply, zero_smul, Finset.sum_const_zero, zero_add,
    PiLp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- A position derivative of the left symbol is the left symbol of the position derivative. -/
private theorem HasCompactSpatialSupport.coordinateDeriv_fst_rightCoeff
    (hc : c.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ rightCoeff c.coefficient (y, ξ)) x =
      rightCoeff (Symbol.spatialDeriv j c).coefficient (x, ξ) := by
  have h := (hc.hasFDerivAt_rightCoeff (x, ξ)).differentiableAt.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x ξ)
  rw [Function.comp_def] at h
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    hc.fderiv_rightCoeff_apply, PiLp.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
    PiLp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Iterated frequency derivatives of the left symbol are left symbols of iterated frequency
derivatives of `c`. -/
private theorem HasCompactSpatialSupport.exists_coordinateDeriv_snd_rightCoeff
    (hc : c.HasCompactSpatialSupport) (β : List (Fin n)) :
    ∃ c' : Symbol n V W (m - β.length), c'.HasCompactSpatialSupport ∧ ∀ x ξ,
      coordinateDeriv β (fun η ↦ rightCoeff c.coefficient (x, η)) ξ =
        rightCoeff c'.coefficient (x, ξ) := by
  induction β with
  | nil => exact ⟨Symbol.inclusion (by simp) c, hc.inclusion _, fun x ξ ↦ by simp⟩
  | cons j β ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨Symbol.inclusion (le_of_eq (by rw [List.length_cons, Nat.cast_succ]; ring))
      (Symbol.frequencyDeriv j c'),
      (hc'.frequencyDeriv j).inclusion _, fun x ξ ↦ ?_⟩
    have hβ : coordinateDeriv β (fun η ↦ rightCoeff c.coefficient (x, η)) =
        fun η ↦ rightCoeff c'.coefficient (x, η) := funext (h x)
    rw [coordinateDeriv_cons, hβ, coefficient_inclusion,
      ← hc'.coordinateDeriv_snd_rightCoeff j x ξ, coordinateDeriv_cons, coordinateDeriv_nil]

/-- Iterated position derivatives of the left symbol are left symbols of iterated position
derivatives of `c`. -/
private theorem HasCompactSpatialSupport.exists_coordinateDeriv_fst_rightCoeff
    (α : List (Fin n)) : ∀ {m : ℝ} {c : Symbol n V W m}, c.HasCompactSpatialSupport →
      ∃ c' : Symbol n V W m, c'.HasCompactSpatialSupport ∧ ∀ x ξ,
        coordinateDeriv α (fun y ↦ rightCoeff c.coefficient (y, ξ)) x =
          rightCoeff c'.coefficient (x, ξ) := by
  induction α with
  | nil => exact fun hc ↦ ⟨_, hc, fun _ _ ↦ by simp⟩
  | cons j α ih =>
    intro m c hc
    obtain ⟨c', hc', h⟩ := ih hc
    refine ⟨Symbol.spatialDeriv j c', hc'.spatialDeriv j, fun x ξ ↦ ?_⟩
    have hα : coordinateDeriv α (fun y ↦ rightCoeff c.coefficient (y, ξ)) =
        fun y ↦ rightCoeff c'.coefficient (y, ξ) := funext fun y ↦ h y ξ
    rw [coordinateDeriv_cons, hα, ← hc'.coordinateDeriv_fst_rightCoeff j x ξ, coordinateDeriv_cons,
      coordinateDeriv_nil]

/-- Every mixed derivative of the left symbol is the left symbol of a symbol of order
`m - |β|` with compact spatial support. -/
private theorem HasCompactSpatialSupport.exists_mixedDeriv_rightCoeff
    (hc : c.HasCompactSpatialSupport) (α β : List (Fin n)) :
    ∃ c' : Symbol n V W (m - β.length), c'.HasCompactSpatialSupport ∧ ∀ x ξ,
      mixedDeriv α β (rightCoeff c.coefficient) x ξ = rightCoeff c'.coefficient (x, ξ) := by
  obtain ⟨c₁, hc₁, h₁⟩ := hc.exists_coordinateDeriv_snd_rightCoeff β
  obtain ⟨c₂, hc₂, h₂⟩ := HasCompactSpatialSupport.exists_coordinateDeriv_fst_rightCoeff α hc₁
  refine ⟨c₂, hc₂, fun x ξ ↦ ?_⟩
  have hβ : (fun y ↦ coordinateDeriv β (fun η ↦ rightCoeff c.coefficient (y, η)) ξ) =
      fun y ↦ rightCoeff c₁.coefficient (y, ξ) := funext fun y ↦ h₁ y ξ
  rw [mixedDeriv_def, hβ, h₂]

/-- The mixed derivatives of the left symbol satisfy the estimates of order `m`, uniformly in the
position. -/
private theorem HasCompactSpatialSupport.exists_norm_mixedDeriv_rightCoeff_le
    (hc : c.HasCompactSpatialSupport) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ, ‖mixedDeriv α β (rightCoeff c.coefficient) x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨c', hc', h⟩ := hc.exists_mixedDeriv_rightCoeff α β
  obtain ⟨C, hC0, hC⟩ := hc'.exists_norm_rightCoeff_le
  exact ⟨C, hC0, fun x ξ ↦ by rw [h]; exact hC (x, ξ)⟩

end Smooth

/-! ### The left symbol of the right quantization -/

section OfRight

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {c : Symbol n V W m}

/-- **The left symbol of the right quantization.** For a symbol `c` of order `m` with compact
spatial support, the symbol
`b(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) dθ`, where `ĉ(θ, ξ)` is the Fourier transform of the
position slice `z ↦ c(z, ξ)`. Its left quantization is the right quantization
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ` of `c`
(`TauCeti.Symbol.quantizeSchwartzValue_ofRight`). It is again a symbol of order `m`, with
estimates uniform in the position (`TauCeti.Symbol.isUniform_ofRight`), but in general it does not
have compact spatial support. -/
def ofRight (c : Symbol n V W m) (hc : c.HasCompactSpatialSupport) : Symbol n V W m where
  coefficient := rightCoeff c.coefficient
  contDiff_coefficient := contDiff_infty.2 fun k ↦ hc.contDiff_rightCoeff k
  exists_bound _ _ α β := by
    obtain ⟨C, hC0, hC⟩ := hc.exists_norm_mixedDeriv_rightCoeff_le α β
    exact ⟨C, hC0, fun x _ ξ ↦ hC x ξ⟩

@[simp]
theorem coefficient_ofRight (hc : c.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    (c.ofRight hc).coefficient (x, ξ) =
      ∫ θ, (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun z ↦ c.coefficient (z, ξ + (2 * π) • θ)) θ :=
  (rfl)

/-- The coefficient of `ofRight` is the private integral `rightCoeff` of this file. -/
private theorem coefficient_ofRight_eq_rightCoeff (hc : c.HasCompactSpatialSupport) :
    (c.ofRight hc).coefficient = rightCoeff c.coefficient :=
  (rfl)

/-- The left symbol of a right quantization satisfies its estimates uniformly in the position. -/
@[simp]
theorem isUniform_ofRight (hc : c.HasCompactSpatialSupport) : (c.ofRight hc).IsUniform :=
  isUniform_iff.2 fun α β ↦ hc.exists_norm_mixedDeriv_rightCoeff_le α β

/-- Position derivatives commute with passing to the left symbol. -/
@[simp]
theorem spatialDeriv_ofRight (hc : c.HasCompactSpatialSupport) (j : Fin n) :
    spatialDeriv j (c.ofRight hc) = (spatialDeriv j c).ofRight (hc.spatialDeriv j) :=
  Symbol.ext (funext fun ⟨x, ξ⟩ ↦ by
    rw [coefficient_spatialDeriv]
    exact hc.coordinateDeriv_fst_rightCoeff j x ξ)

/-- Frequency derivatives commute with passing to the left symbol. -/
@[simp]
theorem frequencyDeriv_ofRight (hc : c.HasCompactSpatialSupport) (j : Fin n) :
    frequencyDeriv j (c.ofRight hc) = (frequencyDeriv j c).ofRight (hc.frequencyDeriv j) :=
  Symbol.ext (funext fun ⟨x, ξ⟩ ↦ by
    rw [coefficient_frequencyDeriv]
    exact hc.coordinateDeriv_snd_rightCoeff j x ξ)

end OfRight

/-! ### The quantization of the left symbol -/

section Quantization

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {c : Symbol n V W m}

/-- **The Fourier transform of a product.** The Fourier transform of `y ↦ c(y, ξ) v(y)` is the
convolution `∫ ĉ(θ, ξ) v̂(ζ - θ) dθ` of the Fourier transforms: by Fourier inversion
`c(y, ξ) v(y) = ∫ exp(2πi ⟪η, y⟫) c(y, ξ) v̂(η) dη`, which is the quantization integral of
`TauCeti.Symbol.HasCompactSpatialSupport.fourier_integral_fourierChar_smul_apply` with the
constant frequency map `η ↦ ξ`. -/
private theorem HasCompactSpatialSupport.fourier_apply_eq_integral
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) (ξ ζ : CoordinateSpace n) :
    𝓕 (fun y ↦ c.coefficient (y, ξ) (v y)) ζ =
      ∫ θ, 𝓕 (fun z ↦ c.coefficient (z, ξ)) θ (𝓕 v (ζ - θ)) := by
  have hv : (fun y ↦ c.coefficient (y, ξ) (v y)) =
      fun y ↦ ∫ η, 𝐞 ⟪η, y⟫ • c.coefficient (y, ξ) (𝓕 v η) := by
    funext y
    have hvint : Integrable fun η ↦ 𝐞 ⟪η, y⟫ • 𝓕 v η :=
      (𝓕 v).integrable.norm.mono' ((by fun_prop : Continuous fun η : CoordinateSpace n ↦
        (𝐞 ⟪η, y⟫ : ℂ)).smul (𝓕 v).continuous).aestronglyMeasurable
        (.of_forall fun η ↦ (Circle.norm_smul _ _).le)
    have hvy : v y = ∫ η, 𝐞 ⟪η, y⟫ • 𝓕 v η := by
      rw [← Real.fourierInv_eq, ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
    rw [hvy, ← (c.coefficient (y, ξ)).integral_comp_comm hvint]
    simp only [Circle.smul_def, map_smul]
  rw [hv, hc.fourier_integral_fourierChar_smul_apply v continuous_const
    ((𝓕 v).integrable.norm.const_mul _), ← integral_sub_left_eq_self _ volume ζ]
  simp only [sub_sub_cancel]

omit [CompleteSpace V] [CompleteSpace W] in
/-- The convolution integrand `(ζ, θ) ↦ ĉ(θ, 2πζ) v̂(ζ - θ)` is integrable. -/
private theorem HasCompactSpatialSupport.integrable_fourier_apply_sub
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun z ↦ c.coefficient (z, (2 * π) • q.1)) q.2 (𝓕 v (q.1 - q.2)))
        (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_fourier_le
  have hg : Integrable fun η : CoordinateSpace n ↦ (1 + ‖η‖ ^ 2) ^ (m / 2) * ‖𝓕 v η‖ :=
    (𝓕 v).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)
  have hconv := (integrable_one_add_norm_rpow_neg_add_one (n := n)).convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) hg (μ := volume) (ν := volume)
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun z ↦ c.coefficient (z, (2 * π) • q.1)) q.2 (𝓕 v (q.1 - q.2)) := by
    have h₁ := hc.continuous_fourier_slice.comp (by fun_prop : Continuous
      fun q : CoordinateSpace n × CoordinateSpace n ↦
        ((q.2, (2 * π) • q.1) : CoordinateSpace n × CoordinateSpace n))
    simp only [Function.comp_def] at h₁
    exact h₁.clm_apply ((𝓕 v).continuous.comp (by fun_prop))
  refine (hconv.const_mul (C * (2 * π) ^ |m| * 2 ^ (|m| / 2))).mono' hcont.aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  obtain ⟨ζ, θ⟩ := q
  dsimp only
  simp only [ContinuousLinearMap.mul_apply']
  have hpeetre := one_add_norm_sq_rpow_le_mul_sub m ζ (ζ - θ)
  rw [sub_sub_cancel] at hpeetre
  have hw := weight_mul_decay_le (m := m) θ
  calc ‖𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ (𝓕 v (ζ - θ))‖
      ≤ ‖𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ‖ * ‖𝓕 v (ζ - θ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * ((2 * π) ^ |m| *
          (2 ^ (|m| / 2) * (1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖ζ - θ‖ ^ 2) ^ (m / 2))) *
          ‖𝓕 v (ζ - θ)‖ := by
        gcongr
        exact (hC θ _).trans (by
          gcongr
          exact (one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) m
            ζ).trans (by gcongr))
    _ = C * (2 * π) ^ |m| * 2 ^ (|m| / 2) * (((1 + ‖θ‖ ^ 2) ^ (|m| / 2) *
          (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|))) *
          ((1 + ‖ζ - θ‖ ^ 2) ^ (m / 2) * ‖𝓕 v (ζ - θ)‖)) := by ring
    _ ≤ C * (2 * π) ^ |m| * 2 ^ (|m| / 2) * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) *
          ((1 + ‖ζ - θ‖ ^ 2) ^ (m / 2) * ‖𝓕 v (ζ - θ)‖)) := by gcongr

omit [CompleteSpace V] [CompleteSpace W] in
/-- The integrand `(η, θ) ↦ exp(2πi ⟪η, x⟫) (exp(2πi ⟪θ, x⟫) ĉ(θ, 2πη + 2πθ)) v̂(η)` of the
quantization of the left symbol is integrable. -/
private theorem HasCompactSpatialSupport.integrable_fourierChar_smul_rightIntegrand_apply
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.1, x⟫ : ℂ) • rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2 (𝓕 v q.1))
        (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_rightIntegrand_le
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.1, x⟫ : ℂ) • rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2 (𝓕 v q.1) := by
    have h₁ := hc.continuous_rightIntegrand.comp (by fun_prop : Continuous
      fun q : CoordinateSpace n × CoordinateSpace n ↦
        (((x, (2 * π) • q.1), q.2) : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n))
    simp only [Function.comp_def] at h₁
    exact (by fun_prop : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.1, x⟫ : ℂ)).smul (h₁.clm_apply ((𝓕 v).continuous.comp continuous_fst))
  have hf : Integrable fun η : CoordinateSpace n ↦
      C * (2 * π) ^ |m| * ((1 + ‖η‖ ^ 2) ^ (m / 2) * ‖𝓕 v η‖) :=
    ((𝓕 v).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul _
  refine (hf.mul_prod integrable_one_add_norm_rpow_neg_add_one).mono' hcont.aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  rw [norm_smul, Circle.norm_coe, one_mul]
  calc ‖rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2 (𝓕 v q.1)‖
      ≤ ‖rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2‖ * ‖𝓕 v q.1‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ((2 * π) ^ |m| * (1 + ‖q.1‖ ^ 2) ^ (m / 2)) * (1 + ‖q.2‖) ^ (-((n : ℝ) + 1)) *
          ‖𝓕 v q.1‖ := by
        gcongr
        exact (hC _ q.2).trans (by
          gcongr
          exact one_add_norm_smul_sq_rpow_le (by linarith [Real.two_le_pi]) m q.1)
    _ = C * (2 * π) ^ |m| * ((1 + ‖q.1‖ ^ 2) ^ (m / 2) * ‖𝓕 v q.1‖) *
          (1 + ‖q.2‖) ^ (-((n : ℝ) + 1)) := by ring

omit [CompleteSpace V] [CompleteSpace W] in
/-- The quantization of the left symbol as an iterated integral of the convolution
integrand. -/
private theorem HasCompactSpatialSupport.quantizeSchwartzValue_ofRight_eq
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (c.ofRight hc).coefficient v x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • ∫ θ, 𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ (𝓕 v (ζ - θ)) := by
  set Φ : CoordinateSpace n × CoordinateSpace n → W := fun q ↦
    (𝐞 ⟪q.1, x⟫ : ℂ) • rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2 (𝓕 v q.1) with hΦ
  have hΦint : Integrable Φ (volume.prod volume) :=
    hc.integrable_fourierChar_smul_rightIntegrand_apply v x
  have hΨ := hc.integrable_fourier_apply_sub v
  have hΨ' : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 ⟪q.1, x⟫ : ℂ) •
      𝓕 (fun z ↦ c.coefficient (z, (2 * π) • q.1)) q.2 (𝓕 v (q.1 - q.2)))
        (volume.prod volume) :=
    hΨ.norm.mono' ((by fun_prop : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.1, x⟫ : ℂ)).aestronglyMeasurable.smul hΨ.aestronglyMeasurable)
      (.of_forall fun q ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  calc quantizeSchwartzValue (c.ofRight hc).coefficient v x = ∫ η, ∫ θ, Φ (η, θ) := by
        rw [quantizeSchwartzValue_def]
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        dsimp only
        rw [coefficient_ofRight_eq_rightCoeff, rightCoeff,
          ContinuousLinearMap.integral_apply (hc.integrable_rightIntegrand _), Circle.smul_def,
          ← integral_smul]
    _ = ∫ θ, ∫ η, Φ (η, θ) := integral_integral_swap hΦint
    _ = ∫ θ, ∫ ζ, (𝐞 ⟪ζ, x⟫ : ℂ) •
          𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ (𝓕 v (ζ - θ)) := by
        refine integral_congr_ae (.of_forall fun θ ↦ ?_)
        dsimp only
        rw [← integral_sub_right_eq_self _ θ]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        simp only [hΦ, rightIntegrand, smul_apply, smul_smul, ← Circle.coe_mul,
          ← AddChar.map_add_eq_mul, ← smul_add, sub_add_cancel, inner_sub_left]
    _ = ∫ ζ, ∫ θ, (𝐞 ⟪ζ, x⟫ : ℂ) •
          𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ (𝓕 v (ζ - θ)) :=
        (integral_integral_swap hΨ').symm
    _ = _ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        dsimp only
        rw [Circle.smul_def, integral_smul]

/-- **The quantization of the left symbol is the right quantization.** For a symbol `c` with
compact spatial support and a Schwartz function `v`,
`Op(c.ofRight hc) v (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ c(y, 2πζ) v(y)) (ζ) dζ`, which in angular
frequency is the right quantization `(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) v(y) dy dξ`. -/
theorem quantizeSchwartzValue_ofRight (hc : c.HasCompactSpatialSupport)
    (v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (c.ofRight hc).coefficient v x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y)) ζ := by
  rw [hc.quantizeSchwartzValue_ofRight_eq]
  simp_rw [hc.fourier_apply_eq_integral]

/-- **The left symbol of the right quantization.** For a symbol `c` with compact spatial support,
the right quantization of `c` on Schwartz space is the quantization of its left symbol
`c.ofRight hc`. -/
theorem quantizeRightUniformCLM_eq_quantizeUniformCLM_ofRight (hc : c.HasCompactSpatialSupport) :
    quantizeRightUniformCLM c hc.isUniform =
      quantizeUniformCLM (c.ofRight hc) (isUniform_ofRight hc) := by
  ext v x
  rw [quantizeRightUniformCLM_apply, quantizeUniformCLM_apply, quantizeSchwartzValue_ofRight]

/-- The frequency profile `ζ ↦ 𝓕 (y ↦ c(y, 2πζ) v(y)) (ζ)` of the right quantization of a symbol
with compact spatial support is integrable. -/
theorem HasCompactSpatialSupport.integrable_fourier_coefficient_apply
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) :
    Integrable fun ζ : CoordinateSpace n ↦
      𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y)) ζ := by
  simp_rw [hc.fourier_apply_eq_integral]
  exact (hc.integrable_fourier_apply_sub v).integral_prod_left

end Quantization

end Symbol

end TauCeti
