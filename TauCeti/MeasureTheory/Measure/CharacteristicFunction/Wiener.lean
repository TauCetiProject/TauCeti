/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Measure.Decomposition.Atomic
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Wiener's lemma on the line

For a finite measure `σ` on `ℝ` with characteristic function `charFun σ t = ∫ exp(itξ) dσ(ξ)`,
the time averages of `|charFun σ t|²` converge to the sum of the squared masses of the atoms of
`σ` (`TauCeti.tendsto_average_norm_charFun_sq`, **Wiener's lemma**):

`T⁻¹ ∫₀ᵀ |charFun σ t|² dt → ∑' ξ, σ({ξ})²` as `T → ∞`.

More generally, for two finite measures `μ` and `ν` the averages of
`charFun μ t * conj (charFun ν t)` converge to the common-atom sum `∑' ξ, μ({ξ}) ν({ξ})`
(`TauCeti.tendsto_average_charFun_mul_conj`). In particular `σ` has no atoms exactly when the
averages of `|charFun σ t|²` tend to `0` (`TauCeti.tendsto_average_norm_charFun_sq_zero_iff`).
This is the criterion through which weak mixing of a measure-preserving flow is read off the
spectral measures of its Koopman group.

Two ingredients are of independent use.

* The twisted averages of a characteristic function recover its atoms
  (`TauCeti.tendsto_average_cexp_mul_charFun`): for every frequency `a`,
  `T⁻¹ ∫₀ᵀ exp(-iat) charFun ρ t dt → ρ({a})`. By Fubini the average is the integral against
  `ρ` of the kernel `T⁻¹ ∫₀ᵀ exp(it(ξ - a)) dt`, which is bounded by `1` and tends to the
  indicator of `{a}`.
* The squared modulus `charFun σ t * conj (charFun σ t)` is the characteristic function of the
  law of `ξ - η` under `σ ⊗ σ` (`TauCeti.charFun_map_sub_prod`), whose mass at `0` is the
  mass `∑' ξ, σ({ξ})²` of the diagonal.

## References

* N. Wiener, *The Fourier Integral and Certain of Its Applications*, Cambridge University Press
  (1933).

* M. Hochman, *Notes on ergodic theory* (2012), Proposition 6.6.3, for the analogue on the circle.
* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press
  (2004), Chapter I, §7, for Wiener's theorem on the Fourier–Stieltjes coefficients of a measure
  on the circle.
-/

public section

open Complex Filter MeasureTheory Topology Set
open scoped RealInnerProductSpace ComplexConjugate

namespace TauCeti

/-- **Atoms from twisted averages of a characteristic function.** For a finite measure `ρ` on `ℝ`
and a frequency `a`, the averages `T⁻¹ ∫₀ᵀ exp(-iat) charFun ρ t dt` converge to the mass
`ρ({a})` as `T → ∞`. -/
theorem tendsto_average_cexp_mul_charFun (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a : ℝ) :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, cexp (-(a * t) * I) * charFun ρ t)
      atTop (𝓝 (ρ.real {a} : ℂ)) := by
  -- By Fubini, the average is the integral against `ρ` of the averaged kernel at `ξ - a`.
  have hcont : Continuous fun p : ℝ × ℝ ↦ cexp (↑(p.1 * (p.2 - a)) * I) := by fun_prop
  have hswap (T : ℝ) : (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, cexp (-(a * t) * I) * charFun ρ t =
      ∫ ξ, (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T, cexp (↑(t * (ξ - a)) * I)) ∂ρ := by
    have : IsFiniteMeasure (volume.restrict (uIoc 0 T)) := by
      rw [uIoc]; infer_instance
    have hint : Integrable (Function.uncurry fun t ξ : ℝ ↦ cexp (↑(t * (ξ - a)) * I))
        ((volume.restrict (uIoc 0 T)).prod ρ) :=
      (integrable_const (1 : ℝ)).mono hcont.aestronglyMeasurable
        (ae_of_all _ fun p ↦ by rw [norm_one]; exact (norm_exp_ofReal_mul_I _).le)
    rw [integral_const_mul]
    congr 1
    refine (intervalIntegral.integral_congr fun t _ ↦ ?_).trans
      (intervalIntegral_integral_swap hint)
    rw [charFun_apply_real, ← integral_const_mul]
    congr 1 with ξ
    rw [← exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hswap]
  have hlim : ∫ ξ, ({0} : Set ℝ).indicator (1 : ℝ → ℂ) (ξ - a) ∂ρ = ρ.real {a} := by
    have : (fun ξ ↦ ({0} : Set ℝ).indicator (1 : ℝ → ℂ) (ξ - a)) =
        ({a} : Set ℝ).indicator fun _ ↦ 1 := by
      ext ξ
      simp [indicator_apply, sub_eq_zero]
    rw [this, integral_indicator_const _ (measurableSet_singleton a), real_smul, mul_one]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (μ := ρ) (fun _ ↦ 1) ?_ ?_
    (integrable_const 1) (ae_of_all _ fun ξ ↦ tendsto_average_integral_cexp (ξ - a))
  · exact Eventually.of_forall fun T ↦ (continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun ξ t ↦ cexp (↑(t * (ξ - a)) * I)) (by fun_prop) 0 T)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with T hT
    refine ae_of_all _ fun ξ ↦ ?_
    rw [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg hT.le, inv_mul_le_one₀ hT]
    exact (norm_integral_cexp_le _ 0 T).trans_eq (by rw [sub_zero, abs_of_pos hT])

/-- The characteristic function of the law of `x - y` under `μ ⊗ ν` is
`charFun μ t * conj (charFun ν t)`. For `ν = μ` it is the squared modulus of `charFun μ t`. -/
theorem charFun_map_sub_prod {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSub₂ E]
    (μ ν : Measure E) [SFinite μ] [SFinite ν] (t : E) :
    charFun ((μ.prod ν).map fun p ↦ p.1 - p.2) t = charFun μ t * conj (charFun ν t) := by
  rw [← charFun_neg, charFun_apply,
    integral_map measurable_sub.aemeasurable (by fun_prop : Continuous _).aestronglyMeasurable]
  simp_rw [charFun_apply, ← integral_prod_mul, inner_sub_left, inner_neg_right, ← exp_add]
  congr 1 with p
  push_cast
  ring_nf

/-- **Bilinear Wiener lemma** on the line: for finite measures `μ` and `ν` on `ℝ`, the time
averages `T⁻¹ ∫₀ᵀ charFun μ t * conj (charFun ν t) dt` converge, as `T → ∞`, to the common-atom
sum `∑' ξ, μ({ξ}) ν({ξ})`. -/
theorem tendsto_average_charFun_mul_conj (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, charFun μ t * conj (charFun ν t))
      atTop (𝓝 ((∑' ξ : ℝ, μ.real {ξ} * ν.real {ξ} : ℝ) : ℂ)) := by
  set ρ := (μ.prod ν).map fun p : ℝ × ℝ ↦ p.1 - p.2
  -- `ρ` gives the point `0`, that is the diagonal of `μ ⊗ ν`, the mass `∑' ξ, μ({ξ}) ν({ξ})`.
  have hρ : ρ.real {0} = ∑' ξ : ℝ, μ.real {ξ} * ν.real {ξ} := by
    rw [map_measureReal_apply measurable_sub (measurableSet_singleton 0)]
    have hpre : (fun p : ℝ × ℝ ↦ p.1 - p.2) ⁻¹' {0} = diagonal ℝ := by
      ext ⟨x, y⟩
      simp [sub_eq_zero]
    rw [hpre, Measure.prod_real_diagonal]
  rw [← hρ]
  refine (tendsto_average_cexp_mul_charFun ρ 0).congr fun T ↦ ?_
  simp only [ofReal_zero, zero_mul, neg_zero, exp_zero, one_mul]
  simp_rw [ρ, charFun_map_sub_prod]

/-- **Wiener's lemma** on the line: for a finite measure `σ` on `ℝ`, the time averages
`T⁻¹ ∫₀ᵀ |charFun σ t|² dt` of the squared modulus of its characteristic function converge, as
`T → ∞`, to the sum `∑' ξ, σ({ξ})²` of the squared masses of its atoms. All but countably many
terms of the sum vanish. -/
theorem tendsto_average_norm_charFun_sq (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2)
      atTop (𝓝 (∑' ξ : ℝ, σ.real {ξ} ^ 2)) := by
  have h := (continuous_re.tendsto _).comp (tendsto_average_charFun_mul_conj σ σ)
  simp_rw [ofReal_re, ← sq] at h
  refine h.congr fun T ↦ ?_
  simp_rw [Function.comp_apply, mul_conj', ← ofReal_pow, intervalIntegral.integral_ofReal,
    ← ofReal_inv, ← ofReal_mul, ofReal_re]

/-- For a finite measure `σ` on `ℝ`, the time averages `T⁻¹ ∫₀ᵀ |charFun σ t|² dt` tend to `0` as
`T → ∞` if and only if `σ` has no atoms. -/
theorem tendsto_average_norm_charFun_sq_zero_iff (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2) atTop (𝓝 0) ↔
      ∀ ξ : ℝ, σ {ξ} = 0 := by
  constructor
  · intro h0 ξ
    have htsum : ∑' x : ℝ, σ.real {x} ^ 2 = 0 :=
      tendsto_nhds_unique (tendsto_average_norm_charFun_sq σ) h0
    have hsum : Summable fun x : ℝ ↦ σ.real {x} ^ 2 := by
      simpa only [sq] using (Measure.hasSum_prod_real_diagonal σ σ).summable
    have hzero : σ.real {ξ} ^ 2 = 0 :=
      le_antisymm (htsum ▸ hsum.le_tsum ξ fun _ _ ↦ sq_nonneg _) (sq_nonneg _)
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
      ((pow_eq_zero_iff (by norm_num)).mp hzero)
  · intro hnull
    have htsum : ∑' ξ : ℝ, σ.real {ξ} ^ 2 = 0 := by
      simp [measureReal_def, hnull]
    simpa only [htsum] using tendsto_average_norm_charFun_sq σ

end TauCeti
