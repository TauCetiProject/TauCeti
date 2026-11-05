/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Pseudodifferential.Symbol

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
formula and proves its basic properties for such coefficients. Apart from the differentiation
results, only the size of `a` enters, so they apply to every symbol class `S^m` through the
estimate `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` with `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)`. Differentiating in the
position also uses the growth of the partial derivative of `a` in the position; for a symbol
`a ∈ S^m_{1,0}` (`TauCeti.Symbol`) every such derivative is again a symbol of order `m`, so
`Op(a) u` is smooth.

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
* `TauCeti.differentiable_quantizeSchwartzValue` and
  `TauCeti.fderiv_quantizeSchwartzValue_apply`: if `a` has a continuous partial derivative `a'`
  in the position, and `a` and `a'` have growth bounds locally uniform in `x`, then `Op(a) u` is
  differentiable with `∂_v Op(a) u = Op(a'(·) v) u + Op(a) (∂_v u)`.
* `TauCeti.Symbol.coordinateDeriv_quantizeSchwartzValue` and
  `TauCeti.Symbol.contDiff_quantizeSchwartzValue`: for a symbol `a`,
  `∂_j Op(a) u = Op(∂_{x_j} a) u + Op(a) (∂_j u)`, and `Op(a) u` is smooth.
* `TauCeti.quantizeSchwartzValue_id`, `TauCeti.quantizeSchwartzValue_comp_fst`,
  `TauCeti.quantizeSchwartzValue_eq_fourierMultiplierCLM` and
  `TauCeti.quantizeSchwartzValue_inner_eq_lineDerivOp`: the quantization of `1` is the
  identity, a position-only coefficient acts by multiplication, a frequency-only coefficient
  gives Mathlib's Fourier multiplier `SchwartzMap.fourierMultiplierCLM` rescaled by `2π`, and
  `ξ ↦ ⟪ξ, v⟫` quantizes to `-i ∂_v`. In particular the differential symbol of `∂_v` is
  `i ⟪ξ, v⟫`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ContDiff
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

/-- The weight `⟨2πζ⟩ ^ m` times the norm of a Schwartz function is integrable. -/
private lemma integrable_weight_mul_norm (m : ℝ) (f : 𝓢(E, V)) :
    Integrable (fun ζ : E ↦ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖f ζ‖) :=
  ((Measure.integrable_pow_neg_integrablePower volume).const_mul _).mono'
    ((((continuous_const.add ((continuous_const_smul _).norm.pow 2)).rpow_const
      fun ζ ↦ Or.inl (by positivity : (1 : ℝ) + ‖(2 * π) • ζ‖ ^ 2 ≠ 0)).mul
        f.continuous.norm).aestronglyMeasurable)
    (ae_of_all _ fun ζ ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact f.one_add_norm_smul_sq_rpow_mul_norm_le (𝕜 := ℂ) (2 * π) m
        (volume : Measure E).integrablePower ζ)

/-- **Pointwise bound.** If `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` at the point `x`, then
`‖Op(a) u (x)‖ ≤ C ∫ ⟨2πζ⟩ ^ m ‖𝓕 u ζ‖ dζ`. -/
theorem norm_quantizeSchwartzValue_le (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (u : 𝓢(E, V)) :
    ‖quantizeSchwartzValue a u x‖ ≤
      C * ∫ ζ, (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ := by
  rw [quantizeSchwartzValue_def, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((integrable_weight_mul_norm m (𝓕 u)).const_mul C)
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

section Derivative

/-! ### Differentiation in the position

Differentiating `exp(2πi ⟪ζ, x⟫) a(x, 2πζ)` in `x` gives `a'(x, 2πζ) v + 2πi ⟪ζ, v⟫ a(x, 2πζ)`
in the direction `v`, and on the Fourier side the factor `2πi ⟪ζ, v⟫` is the derivative `∂_v` of
the input (`SchwartzMap.fourier_lineDerivOp_apply`). Hence
`∂_v Op(a) u = Op(∂_v a) u + Op(a) (∂_v u)`, where `∂_v a` is the partial derivative of the
coefficient in the position. -/

variable {a : E × E → V →L[ℂ] W} {a' : E × E → E →L[ℝ] (V →L[ℂ] W)} {m m' : ℝ}

/-- The partial derivative in the position `x` of the quantization integrand, for a coefficient
`a` with partial derivative `a'` in the position. -/
private def integrandFDeriv (a : E × E → V →L[ℂ] W) (a' : E × E → E →L[ℝ] (V →L[ℂ] W))
    (f : 𝓢(E, V)) (x ζ : E) : E →L[ℝ] W :=
  (𝐞 ⟪ζ, x⟫ : ℂ) • ((ContinuousLinearMap.apply ℂ W (f ζ)).restrictScalars ℝ ∘L a' (x, (2 * π) • ζ)
    + ContinuousLinearMap.smulRightL ℝ E W (innerSL ℝ ζ)
      ((2 * π * Complex.I) • a (x, (2 * π) • ζ) (f ζ)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma integrandFDeriv_apply (f : 𝓢(E, V)) (x ζ v : E) :
    integrandFDeriv a a' f x ζ v = 𝐞 ⟪ζ, x⟫ • a' (x, (2 * π) • ζ) v (f ζ) +
      𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) ((2 * π * Complex.I * ⟪ζ, v⟫) • f ζ) := by
  simp only [integrandFDeriv, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, map_smul, smul_add, Circle.smul_def, ← Complex.coe_smul, smul_smul]
  congr 2
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The quantization integrand has the partial derivative `integrandFDeriv` in the position. -/
private lemma hasFDerivAt_integrand
    (hda : ∀ x ξ, HasFDerivAt (fun y ↦ a (y, ξ)) (a' (x, ξ)) x) (f : 𝓢(E, V)) (x ζ : E) :
    HasFDerivAt (fun y ↦ 𝐞 ⟪ζ, y⟫ • a (y, (2 * π) • ζ) (f ζ)) (integrandFDeriv a a' f x ζ) x := by
  have hc : HasFDerivAt (fun y : E ↦ (𝐞 ⟪ζ, y⟫ : ℂ))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * π * Complex.I * 𝐞 ⟪ζ, x⟫)).comp
        (innerSL ℝ ζ)) x :=
    (Real.hasDerivAt_fourierChar ⟪ζ, x⟫).hasFDerivAt.comp x (innerSL ℝ ζ).hasFDerivAt
  have hg : HasFDerivAt (fun y ↦ a (y, (2 * π) • ζ) (f ζ))
      ((ContinuousLinearMap.apply ℂ W (f ζ)).restrictScalars ℝ ∘L a' (x, (2 * π) • ζ)) x :=
    ((ContinuousLinearMap.apply ℂ W (f ζ)).restrictScalars ℝ).hasFDerivAt.comp x
      (hda x ((2 * π) • ζ))
  simp only [Circle.smul_def]
  refine (hc.smul hg).congr_fderiv ?_
  ext v
  rw [integrandFDeriv_apply]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, one_apply_eq_self,
    Circle.smul_def, map_smul, ← Complex.coe_smul, smul_smul]
  congr 2
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The operator norm bound on the partial derivative of the integrand. -/
private lemma norm_integrandFDeriv_le (f : 𝓢(E, V)) (x ζ : E) :
    ‖integrandFDeriv a a' f x ζ‖ ≤
      (‖a' (x, (2 * π) • ζ)‖ + ‖(2 * π) • ζ‖ * ‖a (x, (2 * π) • ζ)‖) * ‖f ζ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [integrandFDeriv_apply]
  refine (norm_add_le _ _).trans ?_
  rw [Circle.norm_smul, Circle.norm_smul]
  have h₁ : ‖a' (x, (2 * π) • ζ) v (f ζ)‖ ≤ ‖a' (x, (2 * π) • ζ)‖ * ‖v‖ * ‖f ζ‖ :=
    ((a' _ v).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((a' _).le_opNorm v) (norm_nonneg _))
  have h₂ : ‖a (x, (2 * π) • ζ) ((2 * π * Complex.I * ⟪ζ, v⟫) • f ζ)‖ ≤
      ‖(2 * π) • ζ‖ * ‖a (x, (2 * π) • ζ)‖ * ‖v‖ * ‖f ζ‖ := by
    refine ((a _).le_opNorm _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg two_pi_pos.le]
    have hi : ‖(2 * π * Complex.I * ⟪ζ, v⟫ : ℂ)‖ ≤ 2 * π * (‖ζ‖ * ‖v‖) := by
      have h := abs_real_inner_le_norm ζ v
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
        abs_of_pos pi_pos, mul_one]
      gcongr
    calc ‖a (x, (2 * π) • ζ)‖ * (‖(2 * π * Complex.I * ⟪ζ, v⟫ : ℂ)‖ * ‖f ζ‖)
        ≤ ‖a (x, (2 * π) • ζ)‖ * ((2 * π * (‖ζ‖ * ‖v‖)) * ‖f ζ‖) := by gcongr
      _ = 2 * π * ‖ζ‖ * ‖a (x, (2 * π) • ζ)‖ * ‖v‖ * ‖f ζ‖ := by ring
  nlinarith [h₁, h₂]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A norm is at most the weight `⟨·⟩ = (1 + ‖·‖²) ^ (1 / 2)`, so multiplying by it raises the
order of the weight by one. -/
private lemma norm_mul_weight_le (ξ : E) (m : ℝ) :
    ‖ξ‖ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ ((m + 1) / 2) := by
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hle : ‖ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  calc ‖ξ‖ * (1 + ‖ξ‖ ^ 2) ^ (m / 2)
      ≤ (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by gcongr
    _ = (1 + ‖ξ‖ ^ 2) ^ ((m + 1) / 2) := by
        rw [← Real.rpow_add hpos]
        ring_nf

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- At a point where `a` and `a'` satisfy growth bounds, the partial derivative of the integrand is
dominated by an integrable function independent of the point. -/
private lemma norm_integrandFDeriv_le_weight {x : E} {C C' : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ ξ, ‖a' (x, ξ)‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2)) (f : 𝓢(E, V)) (ζ : E) :
    ‖integrandFDeriv a a' f x ζ‖ ≤ C * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m + 1) / 2) * ‖f ζ‖) +
      C' * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m' / 2) * ‖f ζ‖) := by
  refine (norm_integrandFDeriv_le f x ζ).trans ?_
  have h₁ := hC ((2 * π) • ζ)
  have h₂ := hC' ((2 * π) • ζ)
  have h₃ := norm_mul_weight_le ((2 * π) • ζ) m
  have hf := norm_nonneg (f ζ)
  have hn := norm_nonneg ((2 * π) • ζ)
  calc (‖a' (x, (2 * π) • ζ)‖ + ‖(2 * π) • ζ‖ * ‖a (x, (2 * π) • ζ)‖) * ‖f ζ‖
      ≤ (C' * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m' / 2) +
          ‖(2 * π) • ζ‖ * (C * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2))) * ‖f ζ‖ := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h₃ hC0]

omit [MeasurableSpace E] [BorelSpace E] in
private lemma continuous_integrandFDeriv (ha : Continuous a) (ha' : Continuous a') (f : 𝓢(E, V))
    (x : E) : Continuous fun ζ ↦ integrandFDeriv a a' f x ζ := by
  refine continuous_clm_apply.2 fun v ↦ ?_
  simp only [integrandFDeriv_apply]
  have he : Continuous fun ζ : E ↦ 𝐞 ⟪ζ, x⟫ :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  exact (he.smul (((ha'.comp (continuous_const.prodMk (continuous_const_smul _))).clm_apply
    continuous_const).clm_apply f.continuous)).add
    (he.smul ((ha.comp (continuous_const.prodMk (continuous_const_smul _))).clm_apply
      ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_id.inner continuous_const))).smul f.continuous)))

/-- **Differentiation under the integral.** For continuous `a` and `a'` with growth bounds uniform
on compact sets of positions, the quantization has the derivative
`∫ integrandFDeriv a a' (𝓕 u) x₀ ζ dζ` at `x₀`, and this integrand is integrable. -/
private lemma hasFDerivAt_quantizeSchwartzValue_and_integrable (ha : Continuous a)
    (ha' : Continuous a') (hda : ∀ x ξ, HasFDerivAt (fun y ↦ a (y, ξ)) (a' (x, ξ)) x)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a' (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) (x₀ : E) :
    HasFDerivAt (quantizeSchwartzValue a u) (∫ ζ, integrandFDeriv a a' (𝓕 u) x₀ ζ) x₀ ∧
      Integrable (integrandFDeriv a a' (𝓕 u) x₀) := by
  obtain ⟨C, hC⟩ := hC _ (isCompact_closedBall x₀ 1)
  obtain ⟨C', hC'⟩ := hC' _ (isCompact_closedBall x₀ 1)
  have hx₀ := Metric.mem_closedBall_self (x := x₀) zero_le_one
  have hC0 : 0 ≤ C := nonneg_of_norm_le (hC x₀ hx₀)
  have hcont (x : E) : Continuous fun ζ : E ↦ 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 u ζ) :=
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      ((ha.comp (continuous_const.prodMk (continuous_const_smul _))).clm_apply (𝓕 u).continuous)
  have hbound : Integrable fun ζ ↦ C * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m + 1) / 2) * ‖𝓕 u ζ‖) +
      C' * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m' / 2) * ‖𝓕 u ζ‖) :=
    ((integrable_weight_mul_norm _ _).const_mul _).add
      ((integrable_weight_mul_norm _ _).const_mul _)
  refine ⟨?_, hbound.mono' (continuous_integrandFDeriv ha ha' _ x₀).aestronglyMeasurable
    (ae_of_all _ (norm_integrandFDeriv_le_weight hC0 (hC x₀ hx₀) (hC' x₀ hx₀) _))⟩
  simp only [funext (quantizeSchwartzValue_def a u)]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.closedBall_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x ↦ (hcont x).aestronglyMeasurable)
    (integrable_quantizeSchwartzValue_integrand (ha.comp (continuous_const.prodMk continuous_id)
      ).aestronglyMeasurable (hC x₀ hx₀) (𝓕 u))
    (continuous_integrandFDeriv ha ha' _ x₀).aestronglyMeasurable
    (ae_of_all _ fun ζ x hx ↦ norm_integrandFDeriv_le_weight hC0 (hC x hx) (hC' x hx) _ ζ)
    hbound (ae_of_all _ fun ζ x _ ↦ hasFDerivAt_integrand hda (𝓕 u) x ζ)

/-- **Differentiability.** If the coefficient `a` has a partial derivative `a'` in the position,
both are continuous, and both satisfy growth bounds `‖a(x, ξ)‖ ≤ C_K ⟨ξ⟩ ^ m` and
`‖a'(x, ξ)‖ ≤ C'_K ⟨ξ⟩ ^ m'` uniform for `x` in each compact set `K`, then the quantization
`Op(a) u` of a Schwartz function is differentiable. -/
theorem differentiable_quantizeSchwartzValue (ha : Continuous a) (ha' : Continuous a')
    (hda : ∀ x ξ, HasFDerivAt (fun y ↦ a (y, ξ)) (a' (x, ξ)) x)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a' (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) : Differentiable ℝ (quantizeSchwartzValue a u) := fun x ↦
  (hasFDerivAt_quantizeSchwartzValue_and_integrable ha ha' hda hC hC' u x).1.differentiableAt

/-- **The derivative of a quantization.** Under the hypotheses of
`differentiable_quantizeSchwartzValue`, the derivative of `Op(a) u` in the direction `v` is
`∂_v Op(a) u = Op(∂_v a) u + Op(a) (∂_v u)`, where `∂_v a = a'(·) v` is the partial derivative of
the coefficient in the position. -/
theorem fderiv_quantizeSchwartzValue_apply (ha : Continuous a) (ha' : Continuous a')
    (hda : ∀ x ξ, HasFDerivAt (fun y ↦ a (y, ξ)) (a' (x, ξ)) x)
    (hC : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ K : Set E, IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a' (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) (x v : E) :
    fderiv ℝ (quantizeSchwartzValue a u) x v =
      quantizeSchwartzValue (fun p ↦ a' p v) u x + quantizeSchwartzValue a (∂_{v} u) x := by
  obtain ⟨hd, hint⟩ := hasFDerivAt_quantizeSchwartzValue_and_integrable ha ha' hda hC hC' u x
  obtain ⟨C, hCx⟩ := hC {x} isCompact_singleton
  obtain ⟨C', hC'x⟩ := hC' {x} isCompact_singleton
  have hmeas {b : E × E → V →L[ℂ] W} (hb : Continuous b) :
      AEStronglyMeasurable (fun ξ ↦ b (x, ξ)) :=
    (hb.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hint, quantizeSchwartzValue_def,
    quantizeSchwartzValue_def]
  simp only [integrandFDeriv_apply, ← SchwartzMap.fourier_lineDerivOp_apply]
  refine integral_add (integrable_quantizeSchwartzValue_integrand
    (hmeas ((ha'.clm_apply continuous_const : Continuous fun p ↦ a' p v))) (C := C' * ‖v‖)
    (m := m') (fun ξ ↦ ?_) _) (integrable_quantizeSchwartzValue_integrand (hmeas ha)
      (hCx x rfl) _)
  calc ‖a' (x, ξ) v‖ ≤ ‖a' (x, ξ)‖ * ‖v‖ := (a' (x, ξ)).le_opNorm v
    _ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * ‖v‖ := by gcongr; exact hC'x x rfl ξ
    _ = C' * ‖v‖ * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) := by ring

end Derivative

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

/-! ### Quantization of symbols

A symbol `a ∈ S^m_{1,0}` satisfies the hypotheses of `differentiable_quantizeSchwartzValue`, and
its partial derivatives in the position are again symbols of order `m`. Iterating
`∂_j Op(a) u = Op(∂_{x_j} a) u + Op(a) (∂_j u)` shows that `Op(a) u` is smooth. -/

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-- The growth bound of a symbol, uniform on compact sets of positions. -/
private lemma exists_norm_coefficient_le (a : Symbol n V W m) (K : Set (CoordinateSpace n))
    (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, -, hC⟩ := a.exists_bound K hK [] []
  exact ⟨C, fun x hx ξ ↦ by simpa using hC x hx ξ⟩

private lemma hasFDerivAt_coefficient_fst (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    HasFDerivAt (fun y ↦ a.coefficient (y, ξ)) (fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x) x :=
  ((a.contDiff_coefficient.comp (contDiff_prodMk_left ξ)).differentiable (by simp)
    x).hasFDerivAt

private lemma continuous_fderiv_coefficient_fst (a : Symbol n V W m) :
    Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
      fderiv ℝ (fun y ↦ a.coefficient (y, p.2)) p.1 :=
  (ContDiff.fderiv (𝕜 := ℝ) (f := fun p y ↦ a.coefficient (y, p.2)) (n := 0)
    (a.contDiff_coefficient.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)))
    contDiff_fst (by simp)).continuous

/-- The partial derivative of a symbol in the position along a coordinate vector is the
coefficient of its spatial derivative. -/
private lemma fderiv_coefficient_fst_single (a : Symbol n V W m) (j : Fin n) :
    (fun p : CoordinateSpace n × CoordinateSpace n ↦
      fderiv ℝ (fun y ↦ a.coefficient (y, p.2)) p.1 (EuclideanSpace.single j 1)) =
      (spatialDeriv j a).coefficient := by
  funext ⟨x, ξ⟩
  rw [coefficient_spatialDeriv, coordinateDeriv_cons, coordinateDeriv_nil]

/-- The partial derivative of a symbol in the position satisfies the growth bound of order `m`,
uniformly on compact sets of positions. -/
private lemma exists_norm_fderiv_coefficient_fst_le (a : Symbol n V W m)
    (K : Set (CoordinateSpace n)) (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ ξ, ‖fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  choose C hC0 hC using fun j : Fin n ↦ (spatialDeriv j a).exists_bound K hK [] []
  set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  refine ⟨Fintype.card (Fin n) • ‖b.equivFunL.toContinuousLinearMap‖ * ∑ j, C j,
    fun x hx ξ ↦ ?_⟩
  have hw : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by positivity
  refine (b.opNorm_le (M := (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) hw) fun j ↦ ?_).trans_eq (by ring)
  have hj := hC j x hx ξ
  simp only [mixedDeriv_nil_nil, List.length_nil, CharP.cast_eq_zero, sub_zero] at hj
  simp only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  rw [← congrFun (fderiv_coefficient_fst_single a j) (x, ξ)] at hj
  exact hj.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ ↦ hC0 i) (Finset.mem_univ j)) hw)

/-- The quantization `Op(a) u` of a symbol applied to a Schwartz function is differentiable. -/
theorem differentiable_quantizeSchwartzValue (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) : Differentiable ℝ (quantizeSchwartzValue a.coefficient u) :=
  TauCeti.differentiable_quantizeSchwartzValue a.contDiff_coefficient.continuous
    a.continuous_fderiv_coefficient_fst a.hasFDerivAt_coefficient_fst
    a.exists_norm_coefficient_le a.exists_norm_fderiv_coefficient_fst_le u

/-- **Leibniz rule for a quantization.** The coordinate derivative of `Op(a) u` is
`∂_j Op(a) u = Op(∂_{x_j} a) u + Op(a) (∂_j u)`. -/
theorem coordinateDeriv_quantizeSchwartzValue (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (j : Fin n) (x : CoordinateSpace n) :
    coordinateDeriv [j] (quantizeSchwartzValue a.coefficient u) x =
      quantizeSchwartzValue (spatialDeriv j a).coefficient u x +
        quantizeSchwartzValue a.coefficient (∂_{EuclideanSpace.single j (1 : ℝ)} u) x := by
  rw [coordinateDeriv_cons, coordinateDeriv_nil,
    TauCeti.fderiv_quantizeSchwartzValue_apply a.contDiff_coefficient.continuous
      a.continuous_fderiv_coefficient_fst a.hasFDerivAt_coefficient_fst
      a.exists_norm_coefficient_le a.exists_norm_fderiv_coefficient_fst_le,
    fderiv_coefficient_fst_single]

/-- **Smoothness of a quantization.** The quantization `Op(a) u` of a symbol applied to a
Schwartz function is smooth. -/
theorem contDiff_quantizeSchwartzValue (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) :
    ContDiff ℝ ∞ (quantizeSchwartzValue a.coefficient u) := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing a u with
  | zero => exact contDiff_zero.2 (a.differentiable_quantizeSchwartzValue u).continuous
  | succ k ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨a.differentiable_quantizeSchwartzValue u, by simp, fun y ↦ ?_⟩
    have hy : (fun x ↦ fderiv ℝ (quantizeSchwartzValue a.coefficient u) x y) = fun x ↦
        ∑ j, y j • (quantizeSchwartzValue (spatialDeriv j a).coefficient u x +
          quantizeSchwartzValue a.coefficient (∂_{EuclideanSpace.single j (1 : ℝ)} u) x) := by
      funext x
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y]
      simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, map_sum, map_smul,
        ← coordinateDeriv_quantizeSchwartzValue, coordinateDeriv_cons, coordinateDeriv_nil]
    rw [hy]
    exact ContDiff.sum fun j _ ↦ ((ih (spatialDeriv j a) u).add (ih a _)).const_smul (y j)

end Symbol

end TauCeti
