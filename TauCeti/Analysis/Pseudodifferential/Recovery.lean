/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Pseudodifferential.Quantization
import TauCeti.Analysis.Fourier.ChangeOfVariables
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

## References

* R. Melrose, *Pseudodifferential operators on Euclidean space*, Chapter 2, MIT 18.199 (2008),
  §2.8, (2.75)–(2.77): the full symbol is recovered from the operator by testing on
  exponentials.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace Topology
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
    have hphase : Complex.exp (-(⟪x, ξ⟫ * Complex.I)) * 𝐞 ⟪(2 * π)⁻¹ • ξ, x⟫ = 1 := by
      rw [real_inner_comm x, ← exp_inner_mul_I_eq_fourierChar, ← Complex.exp_add]
      simp
    rw [hpull, Circle.smul_def, smul_smul, hphase, one_smul, map_smul]
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

end TauCeti
