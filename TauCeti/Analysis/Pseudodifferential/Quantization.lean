/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# Kohn–Nirenberg quantization on Schwartz functions

For a coefficient map `a : E × E → (V →L[ℂ] W)` of a position `x` and an angular frequency `ξ`,
the left (Kohn–Nirenberg) quantization is formally

`Op(a) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) u(y) dy dξ`.

As a double integral this need not converge absolutely. On Schwartz input it is the single
Fourier integral

`Op(a) u (x) = ∫ exp(2πi ⟪x, ζ⟫) a(x, 2πζ) (𝓕 u ζ) dζ`,

written with Mathlib's Fourier transform `𝓕`, whose phase is `exp(-2πi ⟪x, ζ⟫)`, after the change
of frequency `ξ = 2πζ`, which converges absolutely at `x` whenever `ξ ↦ a(x, ξ)` is a.e. strongly
measurable and of polynomial growth. This file defines `TauCeti.quantizeSchwartzValue` by this
formula and proves its basic properties for such coefficients. Convergence, the bounds and
continuity use only the size of `a`, so they apply to every symbol class `S^m` through the
estimate `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` with `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)`.

Differentiating under the integral sign, a derivative of `Op(a) u` in the position falls either
on the input or on the position variable of the coefficient:
`∂_h (Op(a) u) = Op(a) (∂_h u) + Op(∂ₓ a · h) u`. This needs the same growth bound for the
position derivative `∂ₓ a`. Position derivatives of a symbol `a ∈ S^m` are again symbols of
order `m` (`TauCeti.Symbol.spatialDeriv`), so iterating this rule shows that `Op(a) u` is smooth.

Dually, multiplying `Op(a) u` by a linear function falls either on the input or on the frequency
variable of the coefficient: `⟪x, v⟫ Op(a) u (x) = Op(a) (⟪·, v⟫ u) (x) + i Op(∂_{ξ, v} a) u (x)`.
This is an integration by parts in the frequency, since multiplication by `⟪x, v⟫` is a frequency
derivative of the phase `exp(2πi ⟪ζ, x⟫)`, and multiplication of the input by `⟪·, v⟫` is a
frequency derivative of its Fourier transform.

## Main results

* `TauCeti.quantizeSchwartzValue_eq_smul_integral`: the change-of-frequency equality with the
  angular-frequency formula `(2π)⁻ⁿ ∫ exp(i ⟪x, ξ⟫) a(x, ξ) (∫ exp(-i ⟪y, ξ⟫) u(y) dy) dξ`.
* `TauCeti.integrable_quantizeSchwartzValue_integrand` and
  `TauCeti.norm_quantizeSchwartzValue_le`: absolute convergence and the pointwise bound
  `‖Op(a) u (x)‖ ≤ C ∫ ⟨2πζ⟩ ^ m ‖𝓕 u ζ‖ dζ`.
* `TauCeti.continuous_quantizeSchwartzValue`: `Op(a) u` is continuous for continuous `a` with
  growth bounds locally uniform in `x`.
* `TauCeti.quantizeSchwartzCLM`: for continuous `a` with growth bounds uniform in `x`, the
  quantization is a continuous linear map from Schwartz space to bounded continuous functions.
  `TauCeti.continuous_quantizeSchwartzValue_input` is the pointwise version: `u ↦ Op(a) u (x)`
  is continuous when `ξ ↦ a(x, ξ)` is continuous with a growth bound at the single point `x`.
* `TauCeti.quantizeSchwartzValue_id`, `TauCeti.quantizeSchwartzValue_comp_fst`,
  `TauCeti.quantizeSchwartzValue_eq_fourierMultiplierCLM` and
  `TauCeti.quantizeSchwartzValue_inner_eq_lineDerivOp`: the quantization of `1` is the
  identity, a position-only coefficient acts by multiplication, a frequency-only coefficient
  gives Mathlib's Fourier multiplier `SchwartzMap.fourierMultiplierCLM` rescaled by `2π`, and
  `ξ ↦ ⟪ξ, v⟫` quantizes to `-i ∂_v`. In particular the differential symbol of `∂_v` is
  `i ⟪ξ, v⟫`.
* `TauCeti.quantizeSchwartzValue_arrowCongr`: the quantization is compatible with isomorphisms
  `V ≃L[ℂ] V'` and `W ≃L[ℂ] W'` of the coefficient spaces.
* `TauCeti.Symbol.continuous_quantizeSchwartzValue_coefficient` and
  `TauCeti.Symbol.HasCompactSpatialSupport.memLp_quantizeSchwartzValue`: for a symbol
  `a : TauCeti.Symbol n V W m`, `Op(a) u` is continuous, and if `a` has compact spatial support
  then so does `Op(a) u`, which therefore lies in every `Lᵖ`.
* `TauCeti.differentiable_quantizeSchwartzValue` and
  `TauCeti.fderiv_quantizeSchwartzValue_apply`: `Op(a) u` is differentiable for a `C¹`
  coefficient whose values and position derivatives have growth bounds locally uniform in `x`,
  with `∂_h (Op(a) u) = Op(a) (∂_h u) + Op(∂ₓ a · h) u`.
* `TauCeti.Symbol.coordinateDeriv_quantizeSchwartzValue` and
  `TauCeti.Symbol.contDiff_quantizeSchwartzValue`: for a symbol `a ∈ S^m`, the same rule
  `∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u` for coordinate derivatives, and smoothness
  of `Op(a) u`.
* `TauCeti.inner_smul_quantizeSchwartzValue` and
  `TauCeti.Symbol.ofLp_smul_quantizeSchwartzValue`: `⟪x, v⟫ Op(a) u (x) = Op(a) (⟪·, v⟫ u) (x) +
  i Op(∂_{ξ, v} a) u (x)` for a coefficient that is `C¹` in the frequency with polynomial growth
  at `x`, and `x_j Op(a) u = Op(a) (x_j u) + i Op(∂_{ξ_j} a) u` for a symbol.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv
open MeasureTheory Real FourierTransform Module

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The left (Kohn–Nirenberg) quantization of a coefficient map `a(x, ξ)` evaluated on a Schwartz
function `u` at the point `x`:

`quantizeSchwartzValue a u x = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ`.

The frequency `ξ` of `a` is angular, so the coefficient is evaluated at `2πζ`; see
`quantizeSchwartzValue_eq_smul_integral` for the formula in the variable `ξ`. Integrability is a
separate statement, `integrable_quantizeSchwartzValue_integrand`. -/
def quantizeSchwartzValue (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) : W :=
  ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 u ζ)

theorem quantizeSchwartzValue_def (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a u x = ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 u ζ) :=
  (rfl)

/-- The quantization at `x` only depends on the frequency slice `ξ ↦ a (x, ξ)` of the coefficient
at `x`. -/
theorem quantizeSchwartzValue_congr_left {a b : E × E → V →L[ℂ] W} {x : E}
    (h : ∀ ξ, a (x, ξ) = b (x, ξ)) (u : 𝓢(E, V)) :
    quantizeSchwartzValue a u x = quantizeSchwartzValue b u x := by
  simp only [quantizeSchwartzValue_def, h]

/-- The quantization is the inverse Fourier transform of the rescaled coefficient applied to the
Fourier transform of the input. -/
theorem quantizeSchwartzValue_eq_fourierInv (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a u x = 𝓕⁻ (fun ζ ↦ a (x, (2 * π) • ζ) (𝓕 u ζ)) x := by
  rw [quantizeSchwartzValue_def, Real.fourierInv_eq]

/-- **Change of frequency.** With `n = finrank ℝ E`, the quantization is the angular-frequency
Kohn–Nirenberg integral `(2π)⁻ⁿ ∫ exp(i ⟪x, ξ⟫) a(x, ξ) (∫ exp(-i ⟪y, ξ⟫) u(y) dy) dξ`. -/
theorem quantizeSchwartzValue_eq_smul_integral (a : E × E → V →L[ℂ] W)
    (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a u x = ((2 * π) ^ finrank ℝ E)⁻¹ •
      ∫ ξ, Complex.exp (⟪x, ξ⟫ * Complex.I) •
        a (x, ξ) (∫ y, Complex.exp (-(⟪y, ξ⟫ * Complex.I)) • u y) := by
  have hpos : 0 < ((2 * π) ^ finrank ℝ E)⁻¹ := by positivity
  rw [← abs_of_pos hpos, ← Measure.integral_comp_smul, quantizeSchwartzValue_def]
  congr 1 with ζ
  rw [Circle.smul_def, Real.fourierChar_apply, SchwartzMap.fourier_coe, Real.fourier_eq']
  congr 2
  · simp only [inner_smul_right, real_inner_comm]
  · congr 2 with y
    simp only [inner_smul_right]
    push_cast
    ring_nf

section Bounds

variable {a : E × E → V →L[ℂ] W} {x : E} {C m : ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A growth bound at one point forces the constant to be nonnegative. -/
private lemma nonneg_of_norm_le (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    0 ≤ C := by
  simpa using (norm_nonneg _).trans (hC 0)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise bound on the quantization integrand. -/
private lemma norm_integrand_le (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (f : 𝓢(E, V)) (ζ : E) :
    ‖𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ)‖ ≤
      C * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖f ζ‖) := by
  rw [Circle.norm_smul, ← mul_assoc]
  exact ((a (x, (2 * π) • ζ)).le_opNorm (f ζ)).trans
    (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))

/-- The integrand is dominated by an integrable function, uniformly over every point where the
same growth bound holds. -/
private lemma norm_integrand_le_pow_neg (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (f : 𝓢(E, V)) (ζ : E) :
    ‖𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ)‖ ≤
      C * ((2 * π) ^ ⌈m⌉₊ * 2 ^ (⌈m⌉₊ + (volume : Measure E).integrablePower) *
        (Finset.Iic (⌈m⌉₊ + (volume : Measure E).integrablePower, 0)).sup
          (fun k ↦ SchwartzMap.seminorm ℂ k.1 k.2) f) *
        (1 + ‖ζ‖) ^ (-((volume : Measure E).integrablePower : ℝ)) := by
  refine (norm_integrand_le hC f ζ).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (nonneg_of_norm_le hC)
  have h2π : max 1 |2 * π| = 2 * π := by
    rw [abs_of_pos two_pi_pos, max_eq_right (by linarith [two_le_pi])]
  simpa only [h2π] using f.one_add_norm_smul_sq_rpow_mul_norm_le (2 * π) m
    (volume : Measure E).integrablePower ζ

private lemma aestronglyMeasurable_integrand (hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)))
    (f : 𝓢(E, V)) :
    AEStronglyMeasurable (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ)) := by
  have hscale : AEStronglyMeasurable (fun ζ : E ↦ a (x, (2 * π) • ζ)) :=
    hmeas.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume Real.two_pi_pos.ne')
  exact (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
    ).aestronglyMeasurable.smul (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hscale.prodMk f.continuous.aestronglyMeasurable))

/-- **Absolute convergence.** If `ξ ↦ a(x, ξ)` is a.e. strongly measurable and
`‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` at the point `x`, the quantization integrand at `x` is integrable
against every Schwartz function on the frequency side; with `f = 𝓕 u` this is the integrand of
`quantizeSchwartzValue a u x`. -/
theorem integrable_quantizeSchwartzValue_integrand
    (hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (f : 𝓢(E, V)) :
    Integrable (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ)) :=
  ((Measure.integrable_pow_neg_integrablePower volume).const_mul _).mono'
    (aestronglyMeasurable_integrand hmeas f) (ae_of_all _ (norm_integrand_le_pow_neg hC f))

/-- **Pointwise bound.** If `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` at the point `x`, then
`‖Op(a) u (x)‖ ≤ C ∫ ⟨2πζ⟩ ^ m ‖𝓕 u ζ‖ dζ`. -/
theorem norm_quantizeSchwartzValue_le (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (u : 𝓢(E, V)) :
    ‖quantizeSchwartzValue a u x‖ ≤
      C * ∫ ζ, (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ := by
  rw [quantizeSchwartzValue_def, ← integral_const_mul]
  exact norm_integral_le_of_norm_le
    (((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m).const_mul C)
    (ae_of_all _ (norm_integrand_le hC (𝓕 u)))

private lemma integral_integrand_add (hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (f g : 𝓢(E, V)) :
    ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) ((f + g) ζ) =
      (∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ)) +
        ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (g ζ) := by
  simp only [add_apply, map_add, smul_add]
  exact integral_add (integrable_quantizeSchwartzValue_integrand hmeas hC f)
    (integrable_quantizeSchwartzValue_integrand hmeas hC g)

private lemma integral_integrand_smul (c : ℂ) (f : 𝓢(E, V)) :
    ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) ((c • f) ζ) =
      c • ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ) := by
  simp only [smul_apply, map_smul, smul_comm (𝐞 _) c]
  exact integral_smul c _

/-- The quantization is additive in the input at every point `x` where `ξ ↦ a (x, ξ)` is a.e.
strongly measurable and has a growth bound. -/
theorem quantizeSchwartzValue_add_right (hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (u v : 𝓢(E, V)) :
    quantizeSchwartzValue a (u + v) x = quantizeSchwartzValue a u x + quantizeSchwartzValue a v x
    := by
  simp only [quantizeSchwartzValue_def, FourierTransform.fourier_add]
  exact integral_integrand_add hmeas hC _ _

/-- The quantization is homogeneous in the input. -/
@[simp]
theorem quantizeSchwartzValue_smul_right (c : ℂ) (u : 𝓢(E, V)) :
    quantizeSchwartzValue a (c • u) x = c • quantizeSchwartzValue a u x := by
  simp only [quantizeSchwartzValue_def, FourierTransform.fourier_smul]
  exact integral_integrand_smul c _

/-- The quantization of the zero input vanishes. -/
@[simp]
theorem quantizeSchwartzValue_zero_right :
    quantizeSchwartzValue a (0 : 𝓢(E, V)) x = 0 := by
  simpa using quantizeSchwartzValue_smul_right (a := a) (x := x) 0 0

/-- The quantization is additive in the coefficient at every point `x` where both `ξ ↦ a (x, ξ)`
and `ξ ↦ b (x, ξ)` are a.e. strongly measurable and have growth bounds. -/
theorem quantizeSchwartzValue_add_left {b : E × E → V →L[ℂ] W} {C' m' : ℝ}
    (hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hmeas' : AEStronglyMeasurable (fun ξ ↦ b (x, ξ)))
    (hC' : ∀ ξ, ‖b (x, ξ)‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2)) (u : 𝓢(E, V)) :
    quantizeSchwartzValue (a + b) u x = quantizeSchwartzValue a u x + quantizeSchwartzValue b u x
    := by
  simp only [quantizeSchwartzValue_def, Pi.add_apply, add_apply, smul_add]
  exact integral_add (integrable_quantizeSchwartzValue_integrand hmeas hC _)
    (integrable_quantizeSchwartzValue_integrand hmeas' hC' _)

/-- The quantization is homogeneous in the coefficient. -/
@[simp]
theorem quantizeSchwartzValue_smul_left (c : ℂ) (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (c • a) u x = c • quantizeSchwartzValue a u x := by
  simp only [quantizeSchwartzValue_def, Pi.smul_apply, smul_apply,
    smul_comm (𝐞 _) c]
  exact integral_smul c _

/-- The quantization with the zero coefficient vanishes. -/
@[simp]
theorem quantizeSchwartzValue_zero_left (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (0 : E × E → V →L[ℂ] W) u x = 0 := by
  simp [quantizeSchwartzValue_def]

end Bounds

section Continuity

variable {a : E × E → V →L[ℂ] W} {m : ℝ}

/-- The Fourier-side integral `x ↦ ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (f ζ) dζ` is continuous. -/
private lemma continuous_integral_integrand (ha : Continuous a)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (f : 𝓢(E, V)) :
    Continuous fun x ↦ ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ) := by
  have hcont : Continuous fun p : E × E ↦ 𝐞 ⟪p.2, p.1⟫ • a (p.1, (2 * π) • p.2) (f p.2) :=
    (Real.continuous_fourierChar.comp (continuous_snd.inner continuous_fst)).smul
      ((ha.comp (continuous_fst.prodMk (continuous_snd.const_smul _))).clm_apply
        (f.continuous.comp continuous_snd))
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨C, hC⟩ := hC _ (isCompact_closedBall x₀ 1)
  exact continuousAt_of_dominated
    (Filter.Eventually.of_forall fun x ↦
      (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.mem_of_superset (Metric.closedBall_mem_nhds x₀ one_pos) fun x hx ↦
      ae_of_all _ (norm_integrand_le_pow_neg (hC x hx) f))
    ((Measure.integrable_pow_neg_integrablePower volume).const_mul _)
    (ae_of_all _ fun ζ ↦
      (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt)

/-- **Continuity.** For a continuous coefficient whose growth bound `‖a(x, ξ)‖ ≤ C_K ⟨ξ⟩ ^ m` is
uniform for `x` in each compact set `K`, the quantization `Op(a) u` of a Schwartz function is
continuous. -/
theorem continuous_quantizeSchwartzValue (ha : Continuous a)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (u : 𝓢(E, V)) : Continuous (quantizeSchwartzValue a u) := by
  simp only [funext (quantizeSchwartzValue_def a u)]
  exact continuous_integral_integrand ha hC (𝓕 u)

end Continuity

section Transport

variable {V' W' : Type*} [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

/-- **Change of coefficient spaces.** For isomorphisms `e₁ : V ≃L[ℂ] V'` and `e₂ : W ≃L[ℂ] W'`,
quantizing the conjugated coefficient `e₂ ∘ a(x, ξ) ∘ e₁⁻¹` on `e₁ ∘ u` gives `e₂ ∘ Op(a) u`. -/
theorem quantizeSchwartzValue_arrowCongr (e₁ : V ≃L[ℂ] V') (e₂ : W ≃L[ℂ] W')
    (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (fun p ↦ e₁.arrowCongr e₂ (a p)) (u.postcompCLM (e₁ : V →L[ℂ] V')) x =
      e₂ (quantizeSchwartzValue a u x) := by
  have hF (ζ : E) : 𝓕 (u.postcompCLM (e₁ : V →L[ℂ] V')) ζ = e₁ (𝓕 u ζ) := by
    simp only [SchwartzMap.fourier_coe, Real.fourier_eq, SchwartzMap.postcompCLM_apply,
      ContinuousLinearEquiv.coe_coe, Circle.smul_def, ← map_smul]
    exact e₁.integral_comp_comm _
  simp only [quantizeSchwartzValue_def, hF, ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.symm_apply_apply, Circle.smul_def, ← map_smul]
  exact e₂.integral_comp_comm _

end Transport

section Deriv

/-! ### Differentiation in the position -/

open ContinuousLinearMap

variable {a : E × E → V →L[ℂ] W} {m : ℝ}

/-- The derivative in the position `x` of the quantization integrand
`x ↦ 𝐞 ⟪ζ, x⟫ • a (x, 2πζ) (f ζ)`. -/
private def integrandFDeriv (a : E × E → V →L[ℂ] W) (f : 𝓢(E, V)) (x ζ : E) : E →L[ℝ] W :=
  (𝐞 ⟪ζ, x⟫ : ℂ) • ((apply ℂ W (f ζ)).restrictScalars ℝ ∘L
      fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) x) +
    (toSpanSingleton ℝ (2 * π * Complex.I * 𝐞 ⟪ζ, x⟫) ∘L innerSL ℝ ζ).smulRight
      (a (x, (2 * π) • ζ) (f ζ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma integrandFDeriv_apply (f : 𝓢(E, V)) (x ζ h : E) :
    integrandFDeriv a f x ζ h =
      𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (((2 * π * Complex.I) * ⟪ζ, h⟫) • f ζ) +
        𝐞 ⟪ζ, x⟫ • fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) x h (f ζ) := by
  simp only [integrandFDeriv, add_apply, smul_apply, comp_apply, coe_restrictScalars',
    apply_apply, smulRight_apply, toSpanSingleton_apply, innerSL_apply_apply, map_smul,
    Circle.smul_def, smul_smul, Complex.real_smul]
  rw [add_comm]
  congr 2
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma hasFDerivAt_integrand (ha : ContDiff ℝ 1 a) (f : 𝓢(E, V)) (ζ x : E) :
    HasFDerivAt (fun y ↦ 𝐞 ⟪ζ, y⟫ • a (y, (2 * π) • ζ) (f ζ)) (integrandFDeriv a f x ζ) x := by
  have hg : HasFDerivAt (fun y ↦ a (y, (2 * π) • ζ))
      (fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) x) x :=
    ((ha.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero x).hasFDerivAt
  have hc := (Real.hasDerivAt_fourierChar ⟪ζ, x⟫).hasFDerivAt.comp x
    ((innerSL ℝ ζ).hasFDerivAt (x := x))
  simp only [Circle.smul_def]
  exact hc.smul (((ContinuousLinearMap.apply ℂ W (f ζ)).restrictScalars ℝ).hasFDerivAt.comp x hg)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the integrand is dominated by `⟨2πζ⟩ ^ (m + 1) ‖f ζ‖`: the derivative of
the phase costs one power of the frequency. -/
private lemma norm_integrandFDeriv_le {x : E} {C C' : ℝ}
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ ξ, ‖fderiv ℝ (fun y ↦ a (y, ξ)) x‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (f : 𝓢(E, V)) (ζ : E) :
    ‖integrandFDeriv a f x ζ‖ ≤
      (C + C') * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m + 1) / 2) * ‖f ζ‖) := by
  have hC0 : 0 ≤ C := nonneg_of_norm_le hC
  have hC'0 : 0 ≤ C' := by
    have := (norm_nonneg (fderiv ℝ (fun y ↦ a (y, 0)) x)).trans (hC' 0)
    simpa using this
  set w := (1 + ‖(2 * π) • ζ‖ ^ 2) with hw
  have hζ : 2 * π * ‖ζ‖ = ‖(2 * π) • ζ‖ := by
    rw [norm_smul, Real.norm_of_nonneg two_pi_pos.le]
  refine opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rw [integrandFDeriv_apply]
  refine (norm_add_le _ _).trans ?_
  rw [Circle.norm_smul, Circle.norm_smul]
  have h₁ : ‖a (x, (2 * π) • ζ) (((2 * π * Complex.I) * ⟪ζ, h⟫) • f ζ)‖ ≤
      C * (w ^ (m / 2) * ‖(2 * π) • ζ‖) * ‖f ζ‖ * ‖h‖ := by
    refine ((a _).le_opNorm _).trans ?_
    rw [norm_smul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg pi_pos.le, Complex.norm_I, mul_one, ← hζ]
    have hi : ‖(⟪ζ, h⟫ : ℂ)‖ ≤ ‖ζ‖ * ‖h‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_real_inner_le_norm ζ h
    calc ‖a (x, (2 * π) • ζ)‖ * (2 * π * ‖(⟪ζ, h⟫ : ℂ)‖ * ‖f ζ‖)
        ≤ C * w ^ (m / 2) * (2 * π * (‖ζ‖ * ‖h‖) * ‖f ζ‖) := by gcongr; exact hC _
      _ = C * (w ^ (m / 2) * (2 * π * ‖ζ‖)) * ‖f ζ‖ * ‖h‖ := by ring
  have h₂ : ‖fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) x h (f ζ)‖ ≤
      C' * w ^ (m / 2) * ‖f ζ‖ * ‖h‖ := by
    refine ((fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) x h).le_opNorm _).trans ?_
    calc ‖fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) x h‖ * ‖f ζ‖
        ≤ ‖fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) x‖ * ‖h‖ * ‖f ζ‖ := by gcongr; exact le_opNorm _ _
      _ ≤ C' * w ^ (m / 2) * ‖h‖ * ‖f ζ‖ := by gcongr; exact hC' _
      _ = C' * w ^ (m / 2) * ‖f ζ‖ * ‖h‖ := by ring
  have hw₁ := one_add_norm_sq_rpow_mul_norm_le ((2 * π) • ζ) m
  have hw₂ : w ^ (m / 2) ≤ w ^ ((m + 1) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖(2 * π) • ζ‖]) (by linarith)
  rw [← hw] at hw₁
  calc _ ≤ C * (w ^ (m / 2) * ‖(2 * π) • ζ‖) * ‖f ζ‖ * ‖h‖ + C' * w ^ (m / 2) * ‖f ζ‖ * ‖h‖ :=
        add_le_add h₁ h₂
    _ ≤ C * w ^ ((m + 1) / 2) * ‖f ζ‖ * ‖h‖ + C' * w ^ ((m + 1) / 2) * ‖f ζ‖ * ‖h‖ := by
        gcongr
    _ = (C + C') * (w ^ ((m + 1) / 2) * ‖f ζ‖) * ‖h‖ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
private lemma continuous_integrandFDeriv (ha : ContDiff ℝ 1 a) (f : 𝓢(E, V)) (x : E) :
    Continuous (integrandFDeriv a f x) := by
  have hD : Continuous fun ζ : E ↦ fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) x :=
    (ContDiff.fderiv (f := fun (ζ : E) (y : E) ↦ a (y, (2 * π) • ζ))
      (ha.comp (contDiff_snd.prodMk (contDiff_fst.const_smul _))) contDiff_const
      (n := 0) (by simp)).continuous
  have he : Continuous fun ζ : E ↦ (𝐞 ⟪ζ, x⟫ : ℂ) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))
  have ha' : Continuous fun ζ : E ↦ a (x, (2 * π) • ζ) :=
    ha.continuous.comp (continuous_const.prodMk (continuous_const_smul _))
  refine continuous_clm_apply.2 fun h ↦ ?_
  simp only [integrandFDeriv_apply, Circle.smul_def]
  fun_prop

/-- The derivative of the position integral of the quantization integrand. -/
private lemma hasFDerivAt_integral_integrand (ha : ContDiff ℝ 1 a)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖fderiv ℝ (fun y ↦ a (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (f : 𝓢(E, V)) (x₀ : E) :
    HasFDerivAt (fun x ↦ ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ))
      (∫ ζ, integrandFDeriv a f x₀ ζ) x₀ := by
  obtain ⟨C, hC⟩ := hC _ (isCompact_closedBall x₀ 1)
  obtain ⟨C', hC'⟩ := hC' _ (isCompact_closedBall x₀ 1)
  have hmeas (x : E) : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)) :=
    (ha.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hx₀ : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x ↦ aestronglyMeasurable_integrand (hmeas x) f)
    (integrable_quantizeSchwartzValue_integrand (hmeas x₀) (hC x₀ hx₀) f)
    (continuous_integrandFDeriv ha f x₀).aestronglyMeasurable
    (ae_of_all _ fun ζ x hx ↦ norm_integrandFDeriv_le
      (hC x (Metric.ball_subset_closedBall hx)) (hC' x (Metric.ball_subset_closedBall hx)) f ζ)
    ((f.integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) (m + 1)).const_mul _)
    (ae_of_all _ fun ζ x _ ↦ hasFDerivAt_integrand ha f ζ x)

/-- **Differentiability.** For a `C¹` coefficient whose values and position derivatives have growth
bounds `‖a(x, ξ)‖, ‖∂ₓ a(x, ξ)‖ ≤ C_K ⟨ξ⟩ ^ m` uniform for `x` in each compact set `K`, the
quantization `Op(a) u` of a Schwartz function is differentiable. -/
theorem differentiable_quantizeSchwartzValue (ha : ContDiff ℝ 1 a)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖fderiv ℝ (fun y ↦ a (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (u : 𝓢(E, V)) : Differentiable ℝ (quantizeSchwartzValue a u) := fun x ↦ by
  simp only [funext (quantizeSchwartzValue_def a u)]
  exact (hasFDerivAt_integral_integrand ha hC hC' (𝓕 u) x).differentiableAt

/-- **Leibniz rule.** Under the hypotheses of `differentiable_quantizeSchwartzValue`, the
derivative of `Op(a) u` in a direction `h` is `Op(a) (∂_h u) + Op(∂ₓ a · h) u`: the derivative
falls either on the input or on the position variable of the coefficient. -/
theorem fderiv_quantizeSchwartzValue_apply (ha : ContDiff ℝ 1 a)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖fderiv ℝ (fun y ↦ a (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (u : 𝓢(E, V)) (x h : E) :
    fderiv ℝ (quantizeSchwartzValue a u) x h =
      quantizeSchwartzValue a (∂_{h} u) x +
        quantizeSchwartzValue (fun p ↦ fderiv ℝ (fun y ↦ a (y, p.2)) p.1 h) u x := by
  obtain ⟨C, hCx⟩ := hC _ isCompact_singleton
  obtain ⟨C', hC'x⟩ := hC' _ isCompact_singleton
  have hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)) :=
    (ha.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun ξ ↦ fderiv ℝ (fun y ↦ a (y, ξ)) x h) :=
    ((ContDiff.fderiv (f := fun (ξ : E) (y : E) ↦ a (y, ξ))
      (ha.comp (contDiff_snd.prodMk contDiff_fst)) contDiff_const
      (n := 0) (by simp)).continuous.clm_apply continuous_const).aestronglyMeasurable
  have hCx' : ∀ ξ, ‖fderiv ℝ (fun y ↦ a (y, ξ)) x h‖ ≤ C' * ‖h‖ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
    fun ξ ↦ ((fderiv ℝ (fun y ↦ a (y, ξ)) x).le_opNorm h).trans (by
      rw [mul_right_comm]
      gcongr
      exact hC'x x rfl ξ)
  have hint : Integrable (integrandFDeriv a (𝓕 u) x) :=
    (((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) (m + 1)).const_mul _).mono'
      (continuous_integrandFDeriv ha (𝓕 u) x).aestronglyMeasurable
      (ae_of_all _ (norm_integrandFDeriv_le (hCx x rfl) (hC'x x rfl) (𝓕 u)))
  have hint₁ := integrable_quantizeSchwartzValue_integrand hmeas (hCx x rfl) (𝓕 (∂_{h} u))
  have hint₂ := integrable_quantizeSchwartzValue_integrand
    (a := fun p : E × E ↦ fderiv ℝ (fun y ↦ a (y, p.2)) p.1 h) (x := x) hmeas' hCx' (𝓕 u)
  have hq : quantizeSchwartzValue a u = fun x ↦ ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 u ζ) :=
    funext (quantizeSchwartzValue_def a u)
  rw [hq, (hasFDerivAt_integral_integrand ha hC hC' (𝓕 u) x).fderiv,
    ContinuousLinearMap.integral_apply hint, quantizeSchwartzValue_def,
    quantizeSchwartzValue_def, ← integral_add hint₁ hint₂]
  refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
  simp only [integrandFDeriv_apply, SchwartzMap.fourier_lineDerivOp_apply]

end Deriv

section Weight

/-! ### Multiplication by a linear function -/

variable {a : E × E → V →L[ℂ] W} {x : E} {C C' m m' : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The line derivative in the direction `v` of the phase `ζ ↦ 𝐞 ⟪ζ, x⟫` is
`2πi ⟪v, x⟫ 𝐞 ⟪ζ, x⟫`. This is Mathlib's derivative of `ζ ↦ 𝐞 (-L x ζ)` with `L = -innerSL ℝ`. -/
private lemma hasLineDerivAt_fourierChar_inner (x v ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) ((2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫) ζ v := by
  convert (hasFDerivAt_fourierChar_neg_bilinear_right (-innerSL ℝ) x ζ).hasLineDerivAt v
    using 1 <;> simp [innerSL_apply_apply ℝ, real_inner_comm x]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The line derivative in the direction `v` of the frequency-side integrand
`ζ ↦ a(x, 2πζ) (f ζ)`. -/
private lemma hasLineDerivAt_apply (ha : ContDiff ℝ 1 fun ξ ↦ a (x, ξ)) (f : 𝓢(E, V)) (v ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ a (x, (2 * π) • ζ) (f ζ))
      ((2 * π) • fderiv ℝ (fun ξ ↦ a (x, ξ)) ((2 * π) • ζ) v (f ζ) +
        a (x, (2 * π) • ζ) (∂_{v} f ζ)) ζ v := by
  have hA : HasFDerivAt (fun ζ : E ↦ a (x, (2 * π) • ζ))
      ((fderiv ℝ (fun ξ ↦ a (x, ξ)) ((2 * π) • ζ)).comp ((2 * π) • ContinuousLinearMap.id ℝ E))
      ζ :=
    ((ha.differentiable one_ne_zero _).hasFDerivAt).comp ζ
      ((hasFDerivAt_id ζ).const_smul (2 * π))
  have hf : HasFDerivAt (fun ζ ↦ f ζ) (fderiv ℝ f ζ) ζ :=
    (f.differentiableAt).hasFDerivAt
  have hA' := ((ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).hasFDerivAt).comp ζ hA
  convert (hA'.clm_apply hf).hasLineDerivAt v using 1
  · simp
  · simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_comm]

/-- The integration by parts behind `inner_smul_quantizeSchwartzValue`, before dividing by
`-2πi`. -/
private lemma integral_by_parts_quantizeSchwartzValue (ha : ContDiff ℝ 1 fun ξ ↦ a (x, ξ))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (v : E)
    (hC' : ∀ ξ, ‖fderiv ℝ (fun η ↦ a (x, η)) ξ v‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) :
    (2 * π : ℂ) • quantizeSchwartzValue (fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v) u x +
      (-(2 * π * Complex.I)) • quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (⟪·, v⟫) u) x =
      -((2 * π * Complex.I * ⟪v, x⟫) • quantizeSchwartzValue a u x) := by
  set a' : E × E → V →L[ℂ] W := fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v
  have hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)) := ha.continuous.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun ξ ↦ a' (x, ξ)) :=
    ((ha.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  have hint := integrable_quantizeSchwartzValue_integrand hmeas hC (𝓕 u)
  have hint₁ := integrable_quantizeSchwartzValue_integrand (a := a') hmeas' hC' (𝓕 u)
  have hint₂ := integrable_quantizeSchwartzValue_integrand hmeas hC (∂_{v} (𝓕 u))
  -- integrate by parts in the frequency, moving the derivative from the phase to the rest
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℂ (E := W))
    (f := fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) (f' := fun ζ ↦ (2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫)
    (g := fun ζ ↦ a (x, (2 * π) • ζ) (𝓕 u ζ))
    (g' := fun ζ ↦ (2 * π) • a' (x, (2 * π) • ζ) (𝓕 u ζ) +
      a (x, (2 * π) • ζ) (∂_{v} (𝓕 u) ζ))
    ((hint.smul (2 * π * Complex.I * ⟪v, x⟫ : ℂ)).congr (ae_of_all _ fun ζ ↦ by
      simp [Circle.smul_def, mul_smul]))
    (((hint₁.smul (2 * π)).add hint₂).congr (ae_of_all _ fun ζ ↦ by
      simp [Circle.smul_def, smul_add, smul_comm (2 * π)]))
    (hint.congr (ae_of_all _ fun ζ ↦ by simp [Circle.smul_def]))
    (fun ζ _ ↦ hasLineDerivAt_fourierChar_inner x v ζ)
    (fun ζ _ ↦ hasLineDerivAt_apply ha (𝓕 u) v ζ)
  have h₁ : ∫ ζ, ContinuousLinearMap.lsmul ℝ ℂ (𝐞 ⟪ζ, x⟫ : ℂ)
      ((2 * π) • a' (x, (2 * π) • ζ) (𝓕 u ζ) + a (x, (2 * π) • ζ) (∂_{v} (𝓕 u) ζ)) =
      (2 * π : ℂ) • (∫ ζ, 𝐞 ⟪ζ, x⟫ • a' (x, (2 * π) • ζ) (𝓕 u ζ)) +
        ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (∂_{v} (𝓕 u) ζ) := by
    calc _ = ∫ ζ, (2 * π : ℂ) • (𝐞 ⟪ζ, x⟫ • a' (x, (2 * π) • ζ) (𝓕 u ζ)) +
          𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (∂_{v} (𝓕 u) ζ) :=
          integral_congr_ae (ae_of_all _ fun ζ ↦ by
            simp [Circle.smul_def, smul_add, smul_comm (2 * π : ℂ), ← Complex.coe_smul])
      _ = _ := by
        have hint₁' : Integrable fun ζ ↦ (2 * π : ℂ) • (𝐞 ⟪ζ, x⟫ • a' (x, (2 * π) • ζ) (𝓕 u ζ)) :=
          hint₁.smul _
        rw [integral_add hint₁' hint₂, integral_smul]
  have h₂ : ∫ ζ, ContinuousLinearMap.lsmul ℝ ℂ ((2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫)
      (a (x, (2 * π) • ζ) (𝓕 u ζ)) =
      (2 * π * Complex.I * ⟪v, x⟫) • ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 u ζ) := by
    rw [← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun ζ ↦ by simp [Circle.smul_def, mul_smul])
  rw [h₁, h₂] at hibp
  rw [← quantizeSchwartzValue_smul_right (-(2 * π * Complex.I) : ℂ), quantizeSchwartzValue_def,
    quantizeSchwartzValue_def, quantizeSchwartzValue_def, ← SchwartzMap.lineDerivOp_fourier_eq]
  exact hibp

/-- **Multiplication by a linear function.** If `ξ ↦ a(x, ξ)` is `C¹`, and it and its frequency
derivative in the direction `v` have polynomial growth, then

`⟪x, v⟫ Op(a) u (x) = Op(a) (⟪·, v⟫ u) (x) + i Op(∂_{ξ, v} a) u (x)`,

where `∂_{ξ, v} a (x, ξ) = D_ξ a (x, ξ) v` is the derivative of the coefficient in the frequency.
This is an integration by parts in the frequency: `⟪x, v⟫ exp(2πi ⟪ζ, x⟫)` is a multiple of the
derivative of the phase in the direction `v`, and multiplication of the input by `⟪·, v⟫`
corresponds to the derivative of its Fourier transform in the direction `v`. -/
theorem inner_smul_quantizeSchwartzValue (ha : ContDiff ℝ 1 fun ξ ↦ a (x, ξ))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (v : E)
    (hC' : ∀ ξ, ‖fderiv ℝ (fun η ↦ a (x, η)) ξ v‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) :
    ⟪x, v⟫ • quantizeSchwartzValue a u x =
      quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (⟪·, v⟫) u) x +
        Complex.I • quantizeSchwartzValue (fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v) u x := by
  have key := integral_by_parts_quantizeSchwartzValue ha hC v hC' u
  set a' : E × E → V →L[ℂ] W := fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v
  -- divide `key` by `-2πi`
  have h2πI : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hII : 2 * π * Complex.I * Complex.I = -(2 * π : ℂ) := by
    rw [mul_assoc, Complex.I_mul_I]
    ring
  refine smul_right_injective W h2πI ?_
  beta_reduce
  calc (2 * π * Complex.I) • ⟪x, v⟫ • quantizeSchwartzValue a u x =
        (2 * π * Complex.I * ⟪v, x⟫) • quantizeSchwartzValue a u x := by
        rw [real_inner_comm, ← Complex.coe_smul, smul_smul]
    _ = (2 * π * Complex.I) • quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (⟪·, v⟫) u) x +
        (2 * π * Complex.I * Complex.I) • quantizeSchwartzValue a' u x := by
        rw [hII]
        linear_combination (norm := module) key
    _ = _ := by rw [smul_add, smul_smul]

end Weight

namespace Symbol

/-! ### Smoothness of the quantization of a symbol -/

open scoped ContDiff

variable {n : ℕ} {m : ℝ}

private lemma contDiff_one_coefficient (a : Symbol n V W m) : ContDiff ℝ 1 a.coefficient :=
  a.contDiff_coefficient.of_le (by simp)

/-- **Leibniz rule for symbols.** The coordinate derivative `∂_j` of the quantization of a symbol
`a` is `Op(a) (∂_j u) + Op(∂_{x_j} a) u`. -/
theorem coordinateDeriv_quantizeSchwartzValue (a : Symbol n V W m) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) :
    coordinateDeriv [j] (quantizeSchwartzValue a.coefficient u) =
      quantizeSchwartzValue a.coefficient (∂_{EuclideanSpace.single j (1 : ℝ)} u) +
        quantizeSchwartzValue (spatialDeriv j a).coefficient u := by
  funext x
  rw [coordinateDeriv_cons, coordinateDeriv_nil, fderiv_quantizeSchwartzValue_apply
    a.contDiff_one_coefficient
    (fun K hK ↦ (a.exists_bound_coefficient K hK).imp fun _ h ↦ h.2)
    a.exists_bound_fderiv_coefficient, Pi.add_apply]
  simp only [fderiv_coefficient_single]

/-- **Multiplication by a coordinate function.** For a symbol `a`, the coordinate function `x_j`
times `Op(a) u` is `Op(a) (x_j u) + i Op(∂_{ξ_j} a) u`. -/
theorem ofLp_smul_quantizeSchwartzValue (a : Symbol n V W m) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    x j • quantizeSchwartzValue a.coefficient u x =
      quantizeSchwartzValue a.coefficient
          (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u) x +
        Complex.I • quantizeSchwartzValue (frequencyDeriv j a).coefficient u x := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
  obtain ⟨C', -, hC'⟩ := (frequencyDeriv j a).exists_bound_coefficient {x} isCompact_singleton
  have hcoef : (fun p : CoordinateSpace n × CoordinateSpace n ↦
      fderiv ℝ (fun η ↦ a.coefficient (p.1, η)) p.2 (EuclideanSpace.single j 1)) =
        (frequencyDeriv j a).coefficient := by
    funext p
    rw [← Prod.mk.eta (p := p), coefficient_frequencyDeriv, coordinateDeriv_cons,
      coordinateDeriv_nil]
  have h := inner_smul_quantizeSchwartzValue (a := a.coefficient) (x := x)
    ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).of_le (by simp))
    (fun ξ ↦ hC x rfl ξ) (EuclideanSpace.single j 1)
    (fun ξ ↦ (congrFun hcoef (x, ξ)).symm ▸ hC' x rfl ξ) u
  rw [hcoef] at h
  simpa [EuclideanSpace.inner_single_right] using h

/-- **Smoothness.** The quantization `Op(a) u` of a Schwartz function by a symbol is smooth. -/
theorem contDiff_quantizeSchwartzValue (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) :
    ContDiff ℝ ∞ (quantizeSchwartzValue a.coefficient u) := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing a u with
  | zero =>
    exact contDiff_zero.2 (continuous_quantizeSchwartzValue a.contDiff_coefficient.continuous
      (fun K hK ↦ (a.exists_bound_coefficient K hK).imp fun _ h ↦ h.2) u)
  | succ k ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨differentiable_quantizeSchwartzValue a.contDiff_one_coefficient
      (fun K hK ↦ (a.exists_bound_coefficient K hK).imp fun _ h ↦ h.2)
      a.exists_bound_fderiv_coefficient u, by simp, contDiff_clm_apply_iff.2 fun h ↦ ?_⟩
    -- each partial derivative is again a sum of quantizations of symbols
    have hj (j : Fin n) : ContDiff ℝ k fun x ↦
        fderiv ℝ (quantizeSchwartzValue a.coefficient u) x (EuclideanSpace.single j 1) := by
      have hd : (fun x ↦ fderiv ℝ (quantizeSchwartzValue a.coefficient u) x
          (EuclideanSpace.single j 1)) =
            coordinateDeriv [j] (quantizeSchwartzValue a.coefficient u) := by
        funext x
        rw [coordinateDeriv_cons, coordinateDeriv_nil]
      rw [hd, a.coordinateDeriv_quantizeSchwartzValue j u]
      exact (ih a _).add (ih _ u)
    have hsum : (fun x ↦ fderiv ℝ (quantizeSchwartzValue a.coefficient u) x h) = fun x ↦
        ∑ j, h j •
          fderiv ℝ (quantizeSchwartzValue a.coefficient u) x (EuclideanSpace.single j 1) := by
      funext x
      exact (fderiv ℝ (quantizeSchwartzValue a.coefficient u) x).apply_eq_sum_single h
    rw [hsum]
    exact ContDiff.sum fun j _ ↦ (hj j).const_smul (h j)

end Symbol

section CLM

open scoped BoundedContinuousFunction

variable {a : E × E → V →L[ℂ] W}

/-- The Fourier-side integral is bounded by a finite supremum of Schwartz seminorms of `f`,
uniformly over every point where the same growth bound holds. -/
private lemma norm_integral_integrand_le {x : E} {C m : ℝ}
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (f : 𝓢(E, V)) :
    ‖∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ)‖ ≤
      C * ((2 * π) ^ ⌈m⌉₊ * 2 ^ (⌈m⌉₊ + (volume : Measure E).integrablePower) *
        ∫ ζ : E, (1 + ‖ζ‖) ^ (-((volume : Measure E).integrablePower : ℝ))) *
        (Finset.Iic (⌈m⌉₊ + (volume : Measure E).integrablePower, 0)).sup
          (fun k ↦ SchwartzMap.seminorm ℂ k.1 k.2) f := by
  refine (norm_integral_le_of_norm_le
    ((Measure.integrable_pow_neg_integrablePower volume).const_mul _)
    (ae_of_all _ (norm_integrand_le_pow_neg hC f))).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- The Fourier-side operator `f ↦ (x ↦ ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (f ζ) dζ)`, as a continuous
linear map from Schwartz space to bounded continuous functions. -/
private def fourierSideCLM (ha : Continuous a)
    (hbound : ∃ C m : ℝ, ∀ x ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    𝓢(E, V) →L[ℂ] E →ᵇ W :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun f ↦
      { toFun := fun x ↦ ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (f ζ)
        continuous_toFun := by
          obtain ⟨C, m, hC⟩ := hbound
          exact continuous_integral_integrand ha (fun _ _ ↦ ⟨C, fun x _ ↦ hC x⟩) f
        map_bounded' := by
          obtain ⟨C, m, hC⟩ := hbound
          exact ⟨_, BoundedContinuousFunction.dist_le_two_norm' fun x ↦
            norm_integral_integrand_le (hC x) f⟩ })
    (fun f g ↦ by
      obtain ⟨C, m, hC⟩ := hbound
      ext x
      exact integral_integrand_add (ha.comp (continuous_const.prodMk continuous_id)
        ).aestronglyMeasurable (hC x) f g)
    (fun c f ↦ by ext x; exact integral_integrand_smul c f)
    (by
      obtain ⟨C, m, hC⟩ := hbound
      have hC0 : 0 ≤ C := nonneg_of_norm_le (hC 0)
      refine ⟨_, _, mul_nonneg hC0 (mul_nonneg (by positivity)
        (integral_nonneg fun _ ↦ by positivity)), fun f ↦
          (BoundedContinuousFunction.norm_le (mul_nonneg (mul_nonneg hC0 (mul_nonneg
            (by positivity) (integral_nonneg fun _ ↦ by positivity))) (apply_nonneg _ _))).2
          fun x ↦ norm_integral_integrand_le (hC x) f⟩)

/-- **Continuity in the Schwartz topology.** For a continuous coefficient with a growth bound
`‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` uniform in `x`, the quantization `u ↦ Op(a) u` is a continuous linear map
from Schwartz space to bounded continuous functions. -/
def quantizeSchwartzCLM (ha : Continuous a)
    (hbound : ∃ C m : ℝ, ∀ x ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    𝓢(E, V) →L[ℂ] E →ᵇ W :=
  fourierSideCLM ha hbound ∘L fourierCLM ℂ 𝓢(E, V)

@[simp]
theorem quantizeSchwartzCLM_apply (ha : Continuous a)
    (hbound : ∃ C m : ℝ, ∀ x ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (u : 𝓢(E, V))
    (x : E) : quantizeSchwartzCLM ha hbound u x = quantizeSchwartzValue a u x :=
  (rfl)

/-- **Continuity in the input at a point.** If `ξ ↦ a(x, ξ)` is continuous with a growth bound
`‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` at the point `x`, then `u ↦ Op(a) u (x)` is continuous on Schwartz
space. No regularity in the position is needed. -/
theorem continuous_quantizeSchwartzValue_input {x : E} (hcont : Continuous fun ξ ↦ a (x, ξ))
    {C m : ℝ} (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    Continuous fun u : 𝓢(E, V) ↦ quantizeSchwartzValue a u x := by
  -- Freeze the position at `x`: the frozen coefficient satisfies the global hypotheses of
  -- `quantizeSchwartzCLM` and has the same quantization at `x`.
  have hfrozen : Continuous fun p : E × E ↦ a (x, p.2) := hcont.comp continuous_snd
  refine ((BoundedContinuousFunction.evalCLM ℂ x).comp
    (quantizeSchwartzCLM hfrozen ⟨C, m, fun _ ↦ hC⟩)).continuous.congr fun u ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
    quantizeSchwartzCLM_apply]
  exact quantizeSchwartzValue_congr_left (fun _ ↦ rfl) u

end CLM

section Examples

variable [CompleteSpace V]

/-- A coefficient depending only on the position quantizes to multiplication:
`Op(b(x)) u = b u`. -/
theorem quantizeSchwartzValue_comp_fst [CompleteSpace W] (b : E → V →L[ℂ] W) (u : 𝓢(E, V))
    (x : E) :
    quantizeSchwartzValue (fun p ↦ b p.1) u x = b x (u x) := by
  calc quantizeSchwartzValue (fun p ↦ b p.1) u x = ∫ ζ, b x (𝐞 ⟪ζ, x⟫ • 𝓕 u ζ) := by
        simp only [quantizeSchwartzValue_def, Circle.smul_def, map_smul]
    _ = b x (∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 u ζ) :=
        (b x).integral_comp_comm (by
          simpa [inner_neg_right] using (Real.fourierIntegral_convergent_iff (μ := volume) (-x)).2
            (𝓕 u).integrable)
    _ = b x (u x) := by
        rw [← Real.fourierInv_eq, ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]

/-- The constant coefficient `1` quantizes to the identity: `Op(1) u = u`. -/
@[simp]
theorem quantizeSchwartzValue_id (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (fun _ ↦ ContinuousLinearMap.id ℂ V) u x = u x :=
  quantizeSchwartzValue_comp_fst (fun _ ↦ ContinuousLinearMap.id ℂ V) u x

omit [CompleteSpace V] in
/-- A scalar coefficient depending only on the frequency quantizes to Mathlib's Fourier multiplier
with the frequency rescaled by `2π`. -/
theorem quantizeSchwartzValue_eq_fourierMultiplierCLM {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (fun p ↦ g p.2 • ContinuousLinearMap.id ℂ V) u x =
      SchwartzMap.fourierMultiplierCLM V (fun ζ ↦ g ((2 * π) • ζ)) u x := by
  have hg' : (fun ζ : E ↦ g ((2 * π) • ζ)).HasTemperateGrowth := by fun_prop
  rw [quantizeSchwartzValue_def, SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp [SchwartzMap.smulLeftCLM_apply_apply hg']

/-- The coefficient `ξ ↦ ⟪ξ, v⟫` quantizes to `-i ∂_v`: the operator `D_v = -i ∂_v` has symbol
`⟪ξ, v⟫`, so the differential symbol of `∂_v` is `i ⟪ξ, v⟫`. -/
theorem quantizeSchwartzValue_inner_eq_lineDerivOp (v : E) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (fun p ↦ (⟪p.2, v⟫ : ℂ) • ContinuousLinearMap.id ℂ V) u x =
      -Complex.I • ∂_{v} u x := by
  have h (ζ : E) : ((⟪(2 * π) • ζ, v⟫ : ℝ) : ℂ) • 𝓕 u ζ = -Complex.I • 𝓕 (∂_{v} u) ζ := by
    rw [SchwartzMap.fourier_lineDerivOp_apply, smul_smul, real_inner_smul_left]
    congr 1
    push_cast
    linear_combination (2 * π * ⟪ζ, v⟫ : ℂ) * Complex.I_sq
  calc quantizeSchwartzValue (fun p ↦ (⟪p.2, v⟫ : ℂ) • ContinuousLinearMap.id ℂ V) u x
        = ∫ ζ, 𝐞 ⟪ζ, x⟫ • (-Complex.I • 𝓕 (∂_{v} u) ζ) := by
        simp only [quantizeSchwartzValue_def, smul_apply, ContinuousLinearMap.id_apply, h]
    _ = -Complex.I • ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (∂_{v} u) ζ := by
        simp only [smul_comm (𝐞 _) (-Complex.I)]
        exact integral_smul _ _
    _ = -Complex.I • ∂_{v} u x := by
        rw [← Real.fourierInv_eq, ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]

end Examples

/-! ### Quantization of symbols -/

namespace Symbol

variable {n : ℕ} {m : ℝ} {a : Symbol n V W m}

/-- The quantization `Op(a) u` of a symbol on a Schwartz function is continuous. -/
theorem continuous_quantizeSchwartzValue_coefficient (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) : Continuous (quantizeSchwartzValue a.coefficient u) :=
  continuous_quantizeSchwartzValue a.contDiff_coefficient.continuous
    (fun K hK ↦ (a.exists_bound_coefficient K hK).imp fun _ hC ↦ hC.2) u

/-- The quantization of a symbol with compact spatial support vanishes outside that support. -/
theorem HasCompactSpatialSupport.hasCompactSupport_quantizeSchwartzValue
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V)) :
    HasCompactSupport (quantizeSchwartzValue a.coefficient u) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  exact HasCompactSupport.intro hK fun x hx ↦ by simp [quantizeSchwartzValue_def, hKa x hx]

theorem HasCompactSpatialSupport.integrable_quantizeSchwartzValue
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V)) :
    Integrable (quantizeSchwartzValue a.coefficient u) :=
  (a.continuous_quantizeSchwartzValue_coefficient u).integrable_of_hasCompactSupport
    (ha.hasCompactSupport_quantizeSchwartzValue u)

theorem HasCompactSpatialSupport.memLp_quantizeSchwartzValue
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V)) (p : ENNReal) :
    MemLp (quantizeSchwartzValue a.coefficient u) p :=
  (a.continuous_quantizeSchwartzValue_coefficient u).memLp_of_hasCompactSupport
    (ha.hasCompactSupport_quantizeSchwartzValue u)

end Symbol

end TauCeti
