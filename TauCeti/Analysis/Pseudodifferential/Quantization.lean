/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

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
formula and proves its basic properties for such coefficients. Only the
size of `a` enters: no derivative bounds are used, so the results apply to every symbol class
`S^m` through the estimate `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` with `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)`.

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

/-- The polynomial decay of a Schwartz function absorbs the rescaled weight `⟨2πζ⟩ ^ m`, leaving
an integrable weight `(1 + ‖ζ‖) ^ (-N)` times a finite supremum of Schwartz seminorms. -/
private lemma one_add_norm_smul_sq_rpow_mul_norm_le (m : ℝ) (f : 𝓢(E, V)) (ζ : E) :
    (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖f ζ‖ ≤
      (2 * π) ^ ⌈m⌉₊ * 2 ^ (⌈m⌉₊ + (volume : Measure E).integrablePower) *
        (Finset.Iic (⌈m⌉₊ + (volume : Measure E).integrablePower, 0)).sup
          (fun k ↦ SchwartzMap.seminorm ℂ k.1 k.2) f *
        (1 + ‖ζ‖) ^ (-((volume : Measure E).integrablePower : ℝ)) := by
  set K := ⌈m⌉₊
  set N := (volume : Measure E).integrablePower
  set S := (Finset.Iic (K + N, 0)).sup (fun k ↦ SchwartzMap.seminorm ℂ k.1 k.2) f
  set t := ‖(2 * π) • ζ‖
  have ht : t = 2 * π * ‖ζ‖ := by
    simp [t, norm_smul]
  have hζ : 0 < 1 + ‖ζ‖ := by positivity
  -- The bracket of order `m` is dominated by a polynomial weight of degree `K = ⌈m⌉₊`.
  have hweight : (1 + t ^ 2) ^ (m / 2) ≤ (2 * π) ^ K * (1 + ‖ζ‖) ^ K := by
    calc (1 + t ^ 2) ^ (m / 2) ≤ (1 + t ^ 2) ^ ((K : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith)
            (by gcongr; exact Nat.le_ceil m)
      _ ≤ ((1 + t) ^ 2) ^ ((K : ℝ) / 2) := by
          gcongr
          nlinarith [norm_nonneg ((2 * π) • ζ)]
      _ = (1 + t) ^ K := by
          rw [← Real.rpow_natCast (1 + t) 2, ← Real.rpow_mul (by positivity),
            show ((2 : ℕ) : ℝ) * ((K : ℝ) / 2) = (K : ℝ) by push_cast; ring, Real.rpow_natCast]
      _ ≤ (2 * π * (1 + ‖ζ‖)) ^ K := by
          gcongr
          rw [ht]
          nlinarith [Real.two_le_pi, norm_nonneg ζ]
      _ = (2 * π) ^ K * (1 + ‖ζ‖) ^ K := mul_pow _ _ _
  -- The Schwartz function decays like `(1 + ‖ζ‖) ^ (-(K + N))`.
  have hdecay : (1 + ‖ζ‖) ^ (K + N) * ‖f ζ‖ ≤ 2 ^ (K + N) * S := by
    simpa using f.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K + N, 0)) le_rfl le_rfl ζ
  have hsplit : (1 + ‖ζ‖) ^ K =
      (1 + ‖ζ‖) ^ (-(N : ℝ)) * (1 + ‖ζ‖) ^ (K + N) := by
    rw [Real.rpow_neg hζ.le, Real.rpow_natCast, pow_add]
    field_simp
  calc (1 + t ^ 2) ^ (m / 2) * ‖f ζ‖ ≤ (2 * π) ^ K * (1 + ‖ζ‖) ^ K * ‖f ζ‖ := by gcongr
    _ = (2 * π) ^ K * (1 + ‖ζ‖) ^ (-(N : ℝ)) * ((1 + ‖ζ‖) ^ (K + N) * ‖f ζ‖) := by
        rw [hsplit]; ring
    _ ≤ (2 * π) ^ K * (1 + ‖ζ‖) ^ (-(N : ℝ)) * (2 ^ (K + N) * S) := by gcongr
    _ = _ := by ring

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
  exact mul_le_mul_of_nonneg_left (one_add_norm_smul_sq_rpow_mul_norm_le m f ζ)
    (nonneg_of_norm_le hC)

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
  have hint : Integrable (fun ζ : E ↦ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) :=
    ((Measure.integrable_pow_neg_integrablePower volume).const_mul _).mono'
      ((((continuous_const.add ((continuous_const_smul _).norm.pow 2)).rpow_const
        fun ζ ↦ Or.inl (by positivity : (1 : ℝ) + ‖(2 * π) • ζ‖ ^ 2 ≠ 0)).mul
          (𝓕 u).continuous.norm).aestronglyMeasurable)
      (ae_of_all _ fun ζ ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact one_add_norm_smul_sq_rpow_mul_norm_le m (𝓕 u) ζ)
  rw [quantizeSchwartzValue_def, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hint.const_mul C)
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

/-- The quantization is additive in the input, wherever the coefficient has a growth bound. -/
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

/-- The quantization is additive in the coefficient, wherever both coefficients have growth
bounds. -/
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

end TauCeti
