/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Pseudodifferential.Symbol.HighFrequency
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Recovering the full symbol from exponentials

The left quantization `Op(a)` of a coefficient `a(x, ξ)` acts on the exponential
`e_ξ(y) = exp(i ⟪y, ξ⟫)` by multiplication with the symbol:

`a(x, ξ) = exp(-i ⟪x, ξ⟫) Op(a) (e_ξ) (x)`,

which inverts the full-symbol map. The exponential is not a Schwartz function: its Fourier
transform is the point mass at the frequency `ξ / 2π`. This file makes the identity precise on
Schwartz inputs whose Fourier transforms concentrate at that point. For a Schwartz function `φ`
and a nonzero `ε`, the *cut-off exponential*

`SchwartzMap.cutoffExponential φ ε ξ v : y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v`

is a Schwartz function with Fourier transform `|ε|⁻ⁿ 𝓕 φ (ε⁻¹ (ζ - ξ / 2π)) v`, an approximate
identity at `ξ / 2π` as `ε → 0` (`SchwartzMap.fourier_cutoffExponential`). Hence

`exp(-i ⟪x, ξ⟫) Op(a) (φ.cutoffExponential ε ξ v) (x) → φ(0) a(x, ξ) v` as `ε → 0`,

as soon as `ζ ↦ a(x, ζ)` is a.e. strongly measurable, continuous at `ξ` and of polynomial growth
(`TauCeti.tendsto_quantizeSchwartzValue_cutoffExponential`). For a symbol `a` and `φ(0) = 1`
this recovers every value of the full symbol from the operator
(`TauCeti.Symbol.tendsto_quantizeSchwartzValue_cutoffExponential`). The recovery is exact for
the full quantization: no quotient by smoothing operators is involved.

The proof changes variables `ζ = ξ / 2π + ε η` in the quantization integral, which gives the
exact formula
`Op(a) (φ.cutoffExponential ε ξ v) (x) = ∫ exp(2πi ⟪ξ / 2π + ε η, x⟫) a(x, ξ + 2πε η) (𝓕 φ η) v dη`
(`TauCeti.quantizeSchwartzValue_cutoffExponential`), and then lets `ε → 0` by dominated
convergence. Peetre's inequality bounds the integrand by a multiple of
`⟨2π η⟩ ^ |m| ‖𝓕 φ η‖` for `|ε| ≤ 1`, and `∫ 𝓕 φ = φ(0)` by Fourier inversion.

Removing the phase of the cut-off exponential gives the identity
`exp(-i ⟪x, ξ⟫) Op(a) (φ.cutoffExponential ε ξ v) (x) =
∫ exp(2πi ⟪ε η, x⟫) a(x, ξ + 2πε η) (𝓕 φ η) v dη`
(`TauCeti.exp_smul_quantizeSchwartzValue_cutoffExponential`). For `ε = 1` the cut-off exponential
is the wave packet `y ↦ exp(i ⟪y, ξ⟫) φ(y) v`.

## High-frequency wave packets

The wave packets `u_t(y) = exp(i ⟪y, t ξ⟫) φ(y) v` of a fixed amplitude `φ`, a nonzero frequency
`ξ` and `v ∈ V` recover the principal symbol `σ(a)` of a classical symbol `a` of order `m` as
`t → ∞`, in the sense of Hörmander §18.1. For any symbol `a` of order `m`, the uniform bound
`TauCeti.Symbol.exists_norm_rpow_neg_smul_coefficient_smul_add_le` and the identity above bound
`‖t ^ (-m) Op(a) u_t (x)‖` uniformly for `t ≥ 1` and positions `x` in a compact set
(`TauCeti.Symbol.exists_norm_rpow_neg_smul_quantizeSchwartzValue_cutoffExponential_le`). For a
classical symbol, `TauCeti.ClassicalSymbol.tendsto_rpow_neg_smul_coefficient_smul` and dominated
convergence give

`t ^ (-m) exp(-i ⟪x, t ξ⟫) Op(a) u_t (x) → σ(a)(x, ξ) (φ(x) v)`

(`TauCeti.ClassicalSymbol.tendsto_quantizeSchwartzValue_cutoffExponential_atTop`), and for a
compactly supported amplitude and a Hilbert space `V`

`t ^ (-m) ∫ ⟪Op(a) u_t (x), u_t (x)⟫ dx → ∫ |φ(x)|² ⟪σ(a)(x, ξ) v, v⟫ dx`

(`TauCeti.ClassicalSymbol.tendsto_integral_inner_quantizeSchwartzValue_cutoffExponential`).

## References

* R. Melrose, *Pseudodifferential operators on Euclidean space*, Chapter 2, MIT 18.199 (2008),
  §2.8, (2.75)–(2.77): the full symbol is recovered from the operator by testing on
  exponentials.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap InnerProductSpace RealInnerProductSpace Topology
open MeasureTheory Real FourierTransform Module Filter

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### The quantization of a cut-off exponential -/

/-- **Quantization of a cut-off exponential.** After the change of frequency
`ζ = ξ / 2π + ε η`, the quantization of the cut-off exponential is
`∫ exp(2πi ⟪ξ / 2π + ε η, x⟫) a(x, ξ + 2πε η) (𝓕 φ η) v dη`. -/
theorem quantizeSchwartzValue_cutoffExponential [CompleteSpace V] (a : E × E → V →L[ℂ] W)
    (φ : 𝓢(E, ℂ)) {ε : ℝ} (hε : ε ≠ 0) (ξ : E) (v : V) (x : E) :
    quantizeSchwartzValue a (φ.cutoffExponential ε ξ v) x =
      ∫ η, 𝐞 ⟪(2 * π)⁻¹ • ξ + ε • η, x⟫ • a (x, ξ + (2 * π * ε) • η) (𝓕 φ η • v) := by
  set c : E := (2 * π)⁻¹ • ξ
  set F : E → W := fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 (φ.cutoffExponential ε ξ v) ζ)
  have hscale : |ε ^ finrank ℝ E| * |ε ^ finrank ℝ E|⁻¹ = 1 :=
    mul_inv_cancel₀ (abs_ne_zero.2 (pow_ne_zero _ hε))
  calc quantizeSchwartzValue a (φ.cutoffExponential ε ξ v) x = ∫ ζ, F ζ :=
        quantizeSchwartzValue_def _ _ _
    _ = ∫ ζ, F (c + ζ) := (integral_add_left_eq_self F c).symm
    _ = |ε ^ finrank ℝ E| • ∫ η, F (c + ε • η) := by
        rw [Measure.integral_comp_smul volume (fun ζ ↦ F (c + ζ)), smul_smul, abs_inv,
          hscale, one_smul]
    _ = ∫ η, |ε ^ finrank ℝ E| • F (c + ε • η) := (integral_smul _ _).symm
    _ = _ := by
        congr 1 with η
        have h2π : (2 * π) • (c + ε • η) = ξ + (2 * π * ε) • η := by
          rw [smul_add, smul_inv_smul₀ two_pi_pos.ne', smul_smul]
        have hc : ε⁻¹ • (c + ε • η - (2 * π)⁻¹ • ξ) = η := by
          rw [add_sub_cancel_left, inv_smul_smul₀ hε]
        simp only [F, SchwartzMap.fourier_cutoffExponential φ hε, hc, h2π,
          ContinuousLinearMap.map_smul_of_tower, Circle.smul_def]
        rw [smul_comm (|ε ^ finrank ℝ E|) ((𝐞 _ : ℂ)), smul_smul, hscale, one_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The phase `exp(-i ⟪x, ξ⟫)` cancels the phase `exp(2πi ⟪ξ / 2π, x⟫)`. -/
private lemma exp_neg_mul_I_mul_fourierChar (x ξ : E) :
    Complex.exp (-(⟪x, ξ⟫ * Complex.I)) * 𝐞 ⟪(2 * π)⁻¹ • ξ, x⟫ = 1 := by
  rw [real_inner_comm x, ← exp_inner_mul_I_eq_fourierChar, ← Complex.exp_add]
  simp

/-- **Quantization of a cut-off exponential without its phase.** Removing the phase
`exp(i ⟪x, ζ⟫)`, the quantization of the cut-off exponential `y ↦ exp(i ⟪y, ζ⟫) φ(ε y) v` is the
integral `∫ exp(2πi ⟪ε η, x⟫) a(x, ζ + 2πε η) (𝓕 φ η) v dη`. -/
theorem exp_smul_quantizeSchwartzValue_cutoffExponential [CompleteSpace V]
    (a : E × E → V →L[ℂ] W) (φ : 𝓢(E, ℂ)) {ε : ℝ} (hε : ε ≠ 0) (ζ : E) (v : V) (x : E) :
    Complex.exp (-(⟪x, ζ⟫ * Complex.I)) • quantizeSchwartzValue a (φ.cutoffExponential ε ζ v) x =
      ∫ η, 𝐞 ⟪ε • η, x⟫ • a (x, ζ + (2 * π * ε) • η) (𝓕 φ η • v) := by
  rw [quantizeSchwartzValue_cutoffExponential a φ hε, ← integral_smul]
  congr 1 with η
  simp [inner_add_left, AddChar.map_add_eq_mul, Circle.smul_def, smul_smul, ← mul_assoc,
    exp_neg_mul_I_mul_fourierChar, -mul_inv_rev]

/-! ### Recovery of the symbol -/

section Recovery

variable {a : E × E → V →L[ℂ] W} {x ξ : E} {C m : ℝ}

/-- The integrand of `quantizeSchwartzValue_cutoffExponential`, as a function of the frequency
`η` after the change of variables, is a.e. strongly measurable for every `ε`, including `ε = 0`. -/
private lemma aestronglyMeasurable_integrand_cutoffExponential
    (hmeas : AEStronglyMeasurable (fun ζ ↦ a (x, ζ))) (φ : 𝓢(E, ℂ)) (v : V) (ε : ℝ) :
    AEStronglyMeasurable (fun η ↦
      𝐞 ⟪(2 * π)⁻¹ • ξ + ε • η, x⟫ • a (x, ξ + (2 * π * ε) • η) (𝓕 φ η • v)) := by
  have ha : AEStronglyMeasurable (fun η : E ↦ a (x, ξ + (2 * π * ε) • η)) := by
    rcases eq_or_ne ε 0 with rfl | hε
    · simpa using aestronglyMeasurable_const
    · exact hmeas.comp_quasiMeasurePreserving
        ((measurePreserving_add_left volume ξ).quasiMeasurePreserving.comp
          (Measure.quasiMeasurePreserving_smul volume
            (mul_ne_zero two_pi_pos.ne' hε)))
  exact (Real.continuous_fourierChar.comp ((continuous_const.add
    (continuous_const.smul continuous_id)).inner continuous_const)).aestronglyMeasurable.smul
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (ha.prodMk ((𝓕 φ).continuous.smul continuous_const).aestronglyMeasurable))

/-- For `|ε| ≤ 1` the integrand of `quantizeSchwartzValue_cutoffExponential` is dominated by
`C 2 ^ (|m| / 2) ⟨ξ⟩ ^ m ‖v‖ ⟨2π η⟩ ^ |m| ‖𝓕 φ η‖`, by Peetre's inequality. -/
private lemma norm_integrand_cutoffExponential_le
    (hC : ∀ ζ, ‖a (x, ζ)‖ ≤ C * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) (φ : 𝓢(E, ℂ)) (v : V) {ε : ℝ}
    (hε : |ε| ≤ 1) (η : E) :
    ‖𝐞 ⟪(2 * π)⁻¹ • ξ + ε • η, x⟫ • a (x, ξ + (2 * π * ε) • η) (𝓕 φ η • v)‖ ≤
      C * 2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * ‖v‖ *
        ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) * ‖𝓕 φ η‖) := by
  have hC0 : 0 ≤ C := by
    simpa using (norm_nonneg _).trans (hC 0)
  have hη : ‖(2 * π * ε) • η‖ ≤ ‖(2 * π) • η‖ := by
    rw [norm_smul, norm_smul, norm_mul, Real.norm_of_nonneg two_pi_pos.le, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right two_pi_pos.le hε) (norm_nonneg _)
  have hpeetre : (1 + ‖ξ + (2 * π * ε) • η‖ ^ 2) ^ (m / 2) ≤
      2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) := by
    refine (one_add_norm_add_sq_rpow_le_mul m ξ _).trans ?_
    gcongr
  calc ‖𝐞 ⟪(2 * π)⁻¹ • ξ + ε • η, x⟫ • a (x, ξ + (2 * π * ε) • η) (𝓕 φ η • v)‖
      ≤ ‖a (x, ξ + (2 * π * ε) • η)‖ * (‖𝓕 φ η‖ * ‖v‖) := by
        rw [Circle.norm_smul, ← norm_smul]
        exact (a _).le_opNorm _
    _ ≤ C * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2)) *
        (‖𝓕 φ η‖ * ‖v‖) := by
        gcongr
        exact (hC _).trans (mul_le_mul_of_nonneg_left hpeetre hC0)
    _ = _ := by ring

/-- The integral of `quantizeSchwartzValue_cutoffExponential` depends continuously on `ε` at
`ε = 0`, where it is `exp(2πi ⟪ξ / 2π, x⟫) a(x, ξ) (∫ 𝓕 φ) v`. -/
private lemma tendsto_integral_cutoffExponential
    (hmeas : AEStronglyMeasurable (fun ζ ↦ a (x, ζ))) (hcont : ContinuousAt (fun ζ ↦ a (x, ζ)) ξ)
    (hC : ∀ ζ, ‖a (x, ζ)‖ ≤ C * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) (φ : 𝓢(E, ℂ)) (v : V) :
    Tendsto (fun ε : ℝ ↦
        ∫ η, 𝐞 ⟪(2 * π)⁻¹ • ξ + ε • η, x⟫ • a (x, ξ + (2 * π * ε) • η) (𝓕 φ η • v)) (𝓝 0)
      (𝓝 (∫ η, 𝐞 ⟪(2 * π)⁻¹ • ξ, x⟫ • a (x, ξ) (𝓕 φ η • v))) := by
  refine tendsto_integral_filter_of_dominated_convergence _
    (.of_forall (aestronglyMeasurable_integrand_cutoffExponential hmeas φ v))
    (Filter.eventually_of_mem (Metric.closedBall_mem_nhds (0 : ℝ) one_pos) fun ε hε ↦ .of_forall
      (norm_integrand_cutoffExponential_le hC φ v (by simpa using hε)))
    (((𝓕 φ).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) |m|).const_mul _)
    (.of_forall fun η ↦ ?_)
  have hξ : Tendsto (fun ε : ℝ ↦ ξ + (2 * π * ε) • η) (𝓝 0) (𝓝 ξ) := by
    have h : Continuous fun ε : ℝ ↦ ξ + (2 * π * ε) • η := by fun_prop
    simpa using h.tendsto 0
  have he : Tendsto (fun ε : ℝ ↦ 𝐞 ⟪(2 * π)⁻¹ • ξ + ε • η, x⟫) (𝓝 0)
      (𝓝 (𝐞 ⟪(2 * π)⁻¹ • ξ, x⟫)) := by
    have h : Continuous fun ε : ℝ ↦ 𝐞 ⟪(2 * π)⁻¹ • ξ + ε • η, x⟫ :=
      Real.continuous_fourierChar.comp (by fun_prop)
    simpa using h.tendsto 0
  have ha : Tendsto (fun ε : ℝ ↦ a (x, ξ + (2 * π * ε) • η) (𝓕 φ η • v)) (𝓝 0)
      (𝓝 (a (x, ξ) (𝓕 φ η • v))) :=
    ((ContinuousLinearMap.apply ℂ W (𝓕 φ η • v)).continuous.tendsto _).comp
      (hcont.tendsto.comp hξ)
  exact he.smul ha

variable [CompleteSpace V] [CompleteSpace W]

/-- **Recovery of the full symbol from exponentials.** Let `ζ ↦ a(x, ζ)` be a.e. strongly
measurable with `‖a(x, ζ)‖ ≤ C ⟨ζ⟩ ^ m`, and continuous at `ξ`. Then for every Schwartz `φ` and
`v ∈ V`, as `ε → 0`,

`exp(-i ⟪x, ξ⟫) Op(a) (y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v) (x) → φ(0) a(x, ξ) v`.

For `φ(0) = 1` the quantization of the cut-off exponentials thus recovers `a(x, ξ) v`. -/
theorem tendsto_quantizeSchwartzValue_cutoffExponential
    (hmeas : AEStronglyMeasurable (fun ζ ↦ a (x, ζ))) (hcont : ContinuousAt (fun ζ ↦ a (x, ζ)) ξ)
    (hC : ∀ ζ, ‖a (x, ζ)‖ ≤ C * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) (φ : 𝓢(E, ℂ)) (v : V) :
    Tendsto (fun ε ↦ Complex.exp (-(⟪x, ξ⟫ * Complex.I)) •
        quantizeSchwartzValue a (φ.cutoffExponential ε ξ v) x) (𝓝[≠] 0)
      (𝓝 (φ 0 • a (x, ξ) v)) := by
  have hint : ∫ η, 𝓕 φ η = φ 0 := by
    calc ∫ η, 𝓕 φ η = ∫ η, 𝐞 ⟪η, (0 : E)⟫ • 𝓕 φ η := by simp
      _ = φ 0 := by
        rw [← Real.fourierInv_eq, ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
  have hlim : Complex.exp (-(⟪x, ξ⟫ * Complex.I)) •
      ∫ η, 𝐞 ⟪(2 * π)⁻¹ • ξ, x⟫ • a (x, ξ) (𝓕 φ η • v) = φ 0 • a (x, ξ) v := by
    have hv : Integrable fun η ↦ 𝓕 φ η • v := (𝓕 φ).integrable.smul_const v
    -- Pull the phase and `a (x, ξ)` out of the integral, and use `∫ 𝓕 φ = φ 0`.
    have hpull : ∫ η, 𝐞 ⟪(2 * π)⁻¹ • ξ, x⟫ • a (x, ξ) (𝓕 φ η • v) =
        𝐞 ⟪(2 * π)⁻¹ • ξ, x⟫ • a (x, ξ) (φ 0 • v) := by
      simp_rw [Circle.smul_def]
      rw [integral_smul, (a (x, ξ)).integral_comp_comm hv, integral_smul_const, hint]
    -- The phase `exp(i ⟪x, ξ⟫)` cancels against `exp(-i ⟪x, ξ⟫)`.
    rw [hpull, Circle.smul_def, smul_smul, exp_neg_mul_I_mul_fourierChar, one_smul, map_smul]
  rw [← hlim]
  refine ((tendsto_integral_cutoffExponential hmeas hcont hC φ v).mono_left
    nhdsWithin_le_nhds).const_smul _ |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [quantizeSchwartzValue_cutoffExponential a φ hε]

end Recovery

namespace Symbol

variable [CompleteSpace V] [CompleteSpace W] {n : ℕ} {m : ℝ}

/-- **Recovery of the full symbol.** The coefficient of a symbol is recovered from its
quantization: for a Schwartz `φ` with `φ(0) = 1`,

`exp(-i ⟪x, ξ⟫) Op(a) (y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v) (x) → a(x, ξ) v` as `ε → 0`. -/
theorem tendsto_quantizeSchwartzValue_cutoffExponential (a : Symbol n V W m)
    (x ξ : CoordinateSpace n) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : φ 0 = 1) (v : V) :
    Tendsto (fun ε ↦ Complex.exp (-(⟪x, ξ⟫ * Complex.I)) •
        quantizeSchwartzValue a.coefficient (φ.cutoffExponential ε ξ v) x) (𝓝[≠] 0)
      (𝓝 (a.coefficient (x, ξ) v)) := by
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le {x} isCompact_singleton
  simpa [hφ] using TauCeti.tendsto_quantizeSchwartzValue_cutoffExponential
    (a.continuous_coefficient_slice x).aestronglyMeasurable
    (a.continuous_coefficient_slice x).continuousAt (hC x rfl) φ v

end Symbol

/-! ### High-frequency wave packets -/

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-- The rescaled phase-free quantization of the wave packet of frequency `t ξ` is the integral of
`exp(2πi ⟪η, x⟫) t ^ (-m) a(x, t ξ + 2πη) (𝓕 φ η) v`. -/
private lemma rpow_neg_smul_exp_smul_quantizeSchwartzValue_cutoffExponential [CompleteSpace V]
    (a : Symbol n V W m) (x ξ : CoordinateSpace n) (φ : 𝓢(CoordinateSpace n, ℂ))
    (v : V) (t : ℝ) :
    t ^ (-m) • Complex.exp (-(⟪x, t • ξ⟫ * Complex.I)) •
        quantizeSchwartzValue a.coefficient (φ.cutoffExponential 1 (t • ξ) v) x =
      ∫ η, 𝐞 ⟪η, x⟫ • (t ^ (-m) • a.coefficient (x, t • ξ + (2 * π) • η))
        (𝓕 φ η • v) := by
  rw [exp_smul_quantizeSchwartzValue_cutoffExponential _ φ one_ne_zero, ← integral_smul]
  congr 1 with η
  rw [one_smul, mul_one, smul_apply, smul_comm]

/-- The integrand of `rpow_neg_smul_exp_smul_quantizeSchwartzValue_cutoffExponential` is
dominated by `B ‖v‖ ⟨2πη⟩ ^ |m| ‖𝓕 φ η‖` for `t ≥ 1`. -/
private lemma norm_integrand_le {a : Symbol n V W m} {K : Set (CoordinateSpace n)}
    {ξ : CoordinateSpace n} {B : ℝ}
    (hB : ∀ y ∈ K, ∀ t : ℝ, 1 ≤ t → ∀ ζ : CoordinateSpace n,
      ‖t ^ (-m) • a.coefficient (y, t • ξ + ζ)‖ ≤ B * (1 + ‖ζ‖ ^ 2) ^ (|m| / 2))
    {x : CoordinateSpace n} (hx : x ∈ K) {t : ℝ} (ht : 1 ≤ t) (φ : 𝓢(CoordinateSpace n, ℂ))
    (v : V) (η : CoordinateSpace n) :
    ‖𝐞 ⟪η, x⟫ • (t ^ (-m) • a.coefficient (x, t • ξ + (2 * π) • η)) (𝓕 φ η • v)‖ ≤
      B * ‖v‖ * ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) * ‖𝓕 φ η‖) := by
  rw [Circle.norm_smul]
  refine ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hB x hx t ht ((2 * π) • η)) (norm_nonneg _))).trans_eq ?_
  rw [norm_smul (𝓕 φ η) v]
  ring

/-- **High-frequency wave packets are bounded after rescaling.** For a symbol `a` of order `m`,
a nonzero frequency `ξ`, a Schwartz amplitude `φ` and `v ∈ V`, the quantizations of the wave
packets `u_t(y) = exp(i ⟪y, t ξ⟫) φ(y) v` satisfy `‖t ^ (-m) Op(a) u_t (x)‖ ≤ B` for all `t ≥ 1`
and positions `x` in a compact set. -/
theorem exists_norm_rpow_neg_smul_quantizeSchwartzValue_cutoffExponential_le [CompleteSpace V]
    (a : Symbol n V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) (φ : 𝓢(CoordinateSpace n, ℂ)) (v : V) :
    ∃ B, ∀ x ∈ K, ∀ t : ℝ, 1 ≤ t →
      ‖t ^ (-m) • quantizeSchwartzValue a.coefficient (φ.cutoffExponential 1 (t • ξ) v) x‖ ≤
        B := by
  obtain ⟨B, hB⟩ := a.exists_norm_rpow_neg_smul_coefficient_smul_add_le hK hξ
  refine ⟨∫ η, B * ‖v‖ * ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) * ‖𝓕 φ η‖), fun x hx t ht ↦ ?_⟩
  have h : ‖t ^ (-m) • Complex.exp (-(⟪x, t • ξ⟫ * Complex.I)) •
      quantizeSchwartzValue a.coefficient (φ.cutoffExponential 1 (t • ξ) v) x‖ ≤
        ∫ η, B * ‖v‖ * ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) * ‖𝓕 φ η‖) := by
    rw [rpow_neg_smul_exp_smul_quantizeSchwartzValue_cutoffExponential]
    exact norm_integral_le_of_norm_le
      (((𝓕 φ).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) |m|).const_mul _)
      (.of_forall (norm_integrand_le hB hx ht φ v))
  -- The phase `exp(-i ⟪x, t ξ⟫)` has norm one.
  have hexp : ‖Complex.exp (-(⟪x, t • ξ⟫ * Complex.I))‖ = 1 := by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  rwa [smul_comm (t ^ (-m)), norm_smul, hexp, one_mul] at h


end Symbol

namespace ClassicalSymbol

variable {n : ℕ} {m : ℝ}

/-- **The principal symbol from high-frequency wave packets.** For a classical symbol `a` of order
`m`, a nonzero frequency `ξ`, a Schwartz amplitude `φ` and `v ∈ V`, the wave packets
`u_t(y) = exp(i ⟪y, t ξ⟫) φ(y) v` satisfy

`t ^ (-m) exp(-i ⟪x, t ξ⟫) Op(a) u_t (x) → σ(a)(x, ξ) (φ(x) v)` as `t → ∞`. -/
theorem tendsto_quantizeSchwartzValue_cutoffExponential_atTop [CompleteSpace V] [CompleteSpace W]
    (a : ClassicalSymbol n V W m) (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0)
    (φ : 𝓢(CoordinateSpace n, ℂ)) (v : V) :
    Tendsto (fun t : ℝ ↦ t ^ (-m) • Complex.exp (-(⟪x, t • ξ⟫ * Complex.I)) •
        quantizeSchwartzValue a.toSymbol.coefficient (φ.cutoffExponential 1 (t • ξ) v) x)
      atTop (𝓝 (a.principal.coefficient (x, ξ) (φ x • v))) := by
  obtain ⟨B, hB⟩ :=
    a.toSymbol.exists_norm_rpow_neg_smul_coefficient_smul_add_le isCompact_singleton hξ
  set σ := a.principal.coefficient (x, ξ)
  -- Fourier inversion evaluates the limit integral.
  have hlim : ∫ η, 𝐞 ⟪η, x⟫ • σ (𝓕 φ η • v) = σ (φ x • v) := by
    have h := SchwartzMap.fourierInv_postcompCLM_apply (σ.comp (.toSpanSingleton ℂ v)) (𝓕 φ) x
    rw [fourierInv_fourier_eq, SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
    simpa using h
  rw [← hlim]
  simp_rw [Symbol.rpow_neg_smul_exp_smul_quantizeSchwartzValue_cutoffExponential]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun η ↦ B * ‖v‖ * ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) * ‖𝓕 φ η‖))
    (.of_forall fun t ↦ ?_) ((eventually_ge_atTop 1).mono fun t ht ↦
      .of_forall (Symbol.norm_integrand_le hB rfl ht φ v))
    (((𝓕 φ).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) |m|).const_mul _)
    (.of_forall fun η ↦ ?_)
  · have ha : Continuous fun η : CoordinateSpace n ↦
        t ^ (-m) • a.toSymbol.coefficient (x, t • ξ + (2 * π) • η) :=
      (a.toSymbol.contDiff_coefficient.continuous.comp'
        (by fun_prop : Continuous fun η : CoordinateSpace n ↦ (x, t • ξ + (2 * π) • η))).const_smul
          (t ^ (-m))
    exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      (ha.clm_apply ((𝓕 φ).continuous.smul continuous_const))).aestronglyMeasurable
  -- Pointwise, `t ^ (-m) a(x, t (ξ + t⁻¹ 2πη)) → σ(a)(x, ξ)`.
  have hξη : Tendsto (fun t : ℝ ↦ ξ + t⁻¹ • ((2 * π) • η)) atTop (𝓝 ξ) := by
    have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const ((2 * π) • η)).const_add ξ
    rwa [zero_smul, add_zero] at h
  have ha : Tendsto (fun t : ℝ ↦ t ^ (-m) • a.toSymbol.coefficient (x, t • ξ + (2 * π) • η))
      atTop (𝓝 σ) := by
    refine ((a.tendsto_rpow_neg_smul_coefficient_smul hξ).comp
      (tendsto_id.prodMk (tendsto_const_nhds.prodMk_nhds hξη))).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [smul_add, smul_smul, ht.ne']
  exact ((((ContinuousLinearMap.apply ℂ W (𝓕 φ η • v)).continuous.tendsto _).comp ha).const_smul
    (𝐞 ⟪η, x⟫))

section Inner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Pairings with high-frequency wave packets.** For a classical symbol `a` of order `m`, a
nonzero frequency `ξ`, a compactly supported Schwartz amplitude `φ` and `v ∈ H`, the wave packets
`u_t(y) = exp(i ⟪y, t ξ⟫) φ(y) v` satisfy

`t ^ (-m) ∫ ⟪Op(a) u_t (x), u_t (x)⟫ dx → ∫ |φ(x)|² ⟪σ(a)(x, ξ) v, v⟫ dx` as `t → ∞`. -/
theorem tendsto_integral_inner_quantizeSchwartzValue_cutoffExponential
    (a : ClassicalSymbol n H H m) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0)
    {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ) (v : H) :
    Tendsto (fun t : ℝ ↦ t ^ (-m) • ∫ x, ⟪quantizeSchwartzValue a.toSymbol.coefficient
        (φ.cutoffExponential 1 (t • ξ) v) x, φ.cutoffExponential 1 (t • ξ) v x⟫_ℂ) atTop
      (𝓝 (∫ x, ‖φ x‖ ^ 2 • ⟪a.principal.coefficient (x, ξ) v, v⟫_ℂ)) := by
  set G : ℝ → CoordinateSpace n → H := fun t x ↦
    t ^ (-m) • Complex.exp (-(⟪x, t • ξ⟫ * Complex.I)) •
      quantizeSchwartzValue a.toSymbol.coefficient (φ.cutoffExponential 1 (t • ξ) v) x
  -- The phase of the wave packet cancels in the pairing.
  have hpair : ∀ t x, t ^ (-m) • ⟪quantizeSchwartzValue a.toSymbol.coefficient
      (φ.cutoffExponential 1 (t • ξ) v) x, φ.cutoffExponential 1 (t • ξ) v x⟫_ℂ =
        φ x * ⟪G t x, v⟫_ℂ := by
    intro t x
    simp only [G, SchwartzMap.cutoffExponential_apply φ one_ne_zero, one_smul, inner_smul_right,
      ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, ← Complex.exp_conj, map_neg,
      map_mul, Complex.conj_I, mul_neg, neg_neg]
    ring
  have hlim : ∀ x, φ x * ⟪a.principal.coefficient (x, ξ) (φ x • v), v⟫_ℂ =
      ‖φ x‖ ^ 2 • ⟪a.principal.coefficient (x, ξ) v, v⟫_ℂ := by
    intro x
    rw [map_smul, inner_smul_left, ← mul_assoc, Complex.mul_conj', Complex.real_smul,
      Complex.ofReal_pow]
  simp_rw [← integral_smul, hpair, ← hlim]
  obtain ⟨B, hB⟩ :=
    a.toSymbol.exists_norm_rpow_neg_smul_quantizeSchwartzValue_cutoffExponential_le hφ hξ φ v
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖φ x‖ * (B * ‖v‖))
    (.of_forall fun t ↦ ?_) ((eventually_ge_atTop 1).mono fun t ht ↦ .of_forall fun x ↦ ?_)
    (φ.integrable.norm.mul_const _) (.of_forall fun x ↦ ?_)
  · have hG : Continuous (G t) :=
      ((Complex.continuous_exp.comp (by fun_prop)).smul
        (a.toSymbol.continuous_quantizeSchwartzValue_coefficient _)).const_smul _
    exact (φ.continuous.mul (hG.inner continuous_const)).aestronglyMeasurable
  · by_cases hx : x ∈ tsupport φ
    · rw [norm_mul]
      gcongr
      refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      -- The phase `exp(-i ⟪x, t ξ⟫)` in `G t x` has norm one.
      simp only [G]
      rw [smul_comm (t ^ (-m)), norm_smul, ← neg_mul, ← Complex.ofReal_neg,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      exact hB x hx t ht
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
      exact le_rfl
  · exact ((a.tendsto_quantizeSchwartzValue_cutoffExponential_atTop x hξ φ v).inner
      tendsto_const_nhds).const_mul (φ x)

end Inner

end ClassicalSymbol

end TauCeti
