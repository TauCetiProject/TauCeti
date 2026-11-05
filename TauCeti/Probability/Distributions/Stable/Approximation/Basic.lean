/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic
public import TauCeti.Probability.Distributions.Stable.LevyKhintchine

/-!
# Compensated compound-Poisson approximations to stable laws

Removing a neighbourhood of zero from the stable Lévy measure leaves a finite jump measure.
The corresponding compound-Poisson sum, translated by the negative sine integral over the
retained jumps, is a probability law. Its characteristic function is the exponential of the
truncated compensated Lévy integral. As the cutoff tends to zero these characteristic functions
converge to `exp (stableCharacteristicExponent α β t)`, by the Lévy–Khintchine formula
`integral_exp_sub_one_sub_sin_stableLevyMeasure`.

These laws are the finite-jump approximations used to construct non-Gaussian stable laws by
letting the cutoff tend to zero.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Topology

namespace TauCeti.Probability

/-- The compensated compound-Poisson approximation to a stable law at cutoff `ε`.

The jump rate is the mass of the stable Lévy measure on `{x | ε < |x|}`, and the jump law is
its normalization there. The final translation subtracts the integral of `sin` against the
cutoff Lévy measure. The useful parameter range is `0 < α < 2`, `|β| ≤ 1`, and `0 < ε`. -/
def stableCompensatedPoissonMeasure (α β ε : ℝ) : Measure ℝ :=
  let ν := stableLevyMeasure α β
  let s := {x : ℝ | ε < |x|}
  (compoundPoissonMeasure (ν s).toNNReal (cond ν s)).map
    (fun x ↦ x - ∫ y in s, sin y ∂ν)

/-- The compensated stable approximation is a translated compound-Poisson law. -/
theorem stableCompensatedPoissonMeasure_def (α β ε : ℝ) :
    stableCompensatedPoissonMeasure α β ε =
      (compoundPoissonMeasure
        ((stableLevyMeasure α β) {x : ℝ | ε < |x|}).toNNReal
        (cond (stableLevyMeasure α β) {x : ℝ | ε < |x|})).map
        (fun x ↦ x - ∫ y in {y : ℝ | ε < |y|}, sin y ∂stableLevyMeasure α β) := (rfl)

/-- Every valid compensated stable approximation is a probability measure. -/
theorem isProbabilityMeasure_stableCompensatedPoissonMeasure {α β ε : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) :
    IsProbabilityMeasure (stableCompensatedPoissonMeasure α β ε) := by
  let _ := isProbabilityMeasure_cond_stableLevyMeasure hα hβ hε
  rw [stableCompensatedPoissonMeasure_def]
  infer_instance

/-- The characteristic function of a compensated stable approximation is the exponential of
the truncated compensated Lévy integral. -/
theorem charFun_stableCompensatedPoissonMeasure {α β ε : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (t : ℝ) :
    charFun (stableCompensatedPoissonMeasure α β ε) t =
      Complex.exp (∫ x in {x : ℝ | ε < |x|},
        Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
          (t * sin x : ℝ) * Complex.I ∂stableLevyMeasure α β) := by
  let ν := stableLevyMeasure α β
  let s : Set ℝ := {x | ε < |x|}
  let c : ℝ := ∫ x in s, sin x ∂ν
  have hm0 : ν s ≠ 0 := (stableLevyMeasure_abs_gt_pos hα hβ hε).ne'
  have hm_top : ν s ≠ ∞ := stableLevyMeasure_abs_gt_ne_top hε
  let _ := isProbabilityMeasure_cond_stableLevyMeasure hα hβ hε
  -- First express the characteristic function of the normalized cutoff jump measure
  -- directly as a normalized integral against the unnormalized Lévy measure.
  have hchar_cond : charFun (ProbabilityTheory.cond ν s) t =
      (ν s).toReal⁻¹ * ∫ x in s, Complex.exp ((t * x : ℝ) * Complex.I) ∂ν := by
    rw [charFun_apply_real, ProbabilityTheory.cond, integral_smul_measure,
      ENNReal.toReal_inv, Complex.real_smul, Complex.ofReal_inv]
    simp only [Complex.ofReal_mul]
  have hfinite : IsFiniteMeasure (ν.restrict s) :=
    isFiniteMeasure_stableLevyMeasure_restrict_abs_gt hε
  have hexp : IntegrableOn (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I)) s ν := by
    let _ := hfinite
    exact Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ by
      simpa using (Complex.norm_exp_ofReal_mul_I (t * x)).le)
  have hsin : IntegrableOn (fun x : ℝ ↦ sin x) s ν := by
    let _ := hfinite
    exact Integrable.of_bound (by fun_prop) 1
      (ae_of_all _ fun x ↦ by simpa using abs_sin_le_one x)
  have hone : IntegrableOn (fun _ : ℝ ↦ (1 : ℂ)) s ν := integrableOn_const hm_top
  have hsinC : IntegrableOn (fun x : ℝ ↦ (t * sin x : ℝ) * Complex.I) s ν := by
    apply (hsin.ofReal.const_mul ((t : ℂ) * Complex.I)).congr
    exact ae_of_all _ fun x ↦ by simp only [Complex.ofReal_mul]; ring_nf; rfl
  -- Translation contributes the compensating phase. The compound-Poisson exponent then
  -- cancels the cutoff mass introduced by normalization.
  rw [stableCompensatedPoissonMeasure_def]
  -- The defining equation expands the cutoff measure, set, and compensation integral;
  -- fold those expressions back to the local names used throughout the calculation.
  change charFun ((compoundPoissonMeasure (ν s).toNNReal (cond ν s)).map
    (fun x ↦ x - c)) t = _
  have htranslate : (fun x : ℝ ↦ x - c) = (fun x ↦ x + (-c)) := by
    simp only [sub_eq_add_neg]
  rw [htranslate, charFun_map_add_const,
    charFun_compoundPoissonMeasure (ν s).toNNReal (cond ν s) t,
    hchar_cond, ← Complex.exp_add]
  congr 1
  -- Expand the compensated integral only after establishing integrability of all three terms.
  have hsub₁ := integral_sub (hexp.sub hone) hsinC
  have hsub₂ := integral_sub hexp hone
  simp only [Pi.sub_apply] at hsub₁ hsub₂
  rw [hsub₁, hsub₂, integral_const]
  have hsin_integral :
      ∫ x in s, (t * sin x : ℝ) * Complex.I ∂ν = (t * c : ℝ) * Complex.I := by
    calc
      _ = ((t : ℂ) * Complex.I) * ∫ x in s, (sin x : ℂ) ∂ν := by
        rw [← integral_const_mul]
        congr with x
        push_cast
        ring
      _ = ((t : ℂ) * Complex.I) * (c : ℂ) := by
        congr 1
        exact integral_ofReal
      _ = (t * c : ℝ) * Complex.I := by push_cast; ring
  rw [hsin_integral]
  have hm_real : (ν s).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hm0, hm_top⟩
  have hinner : inner ℝ (-c) t = -t * c := by rw [Real.inner_apply]; ring
  rw [hinner, measureReal_restrict_apply_univ]
  simp only [measureReal_def, ENNReal.coe_toNNReal_eq_toReal, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_mul, mul_one]
  field_simp [hm_real]
  have hJ :
      (∫ x in s, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂ν) =
        ∫ x in s, Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by ring_nf
  rw [hJ]
  ring

/-- As the positive cutoff tends to zero, the characteristic functions of the compensated
compound-Poisson approximations converge to the exponential of the stable characteristic
exponent. -/
theorem tendsto_charFun_stableCompensatedPoissonMeasure {α β : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (t : ℝ) :
    Tendsto (fun ε ↦ charFun (stableCompensatedPoissonMeasure α β ε) t) (𝓝[>] 0)
      (𝓝 (Complex.exp (stableCharacteristicExponent α β t))) := by
  have hlim := (Complex.continuous_exp.tendsto _).comp
    ((tendsto_integral_exp_sub_one_sub_sin_stableLevyMeasure α β t).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  rw [integral_exp_sub_one_sub_sin_stableLevyMeasure hα hβ t] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (charFun_stableCompensatedPoissonMeasure hα hβ hε t).symm

/-- The characteristic functions converge along the dyadic cutoffs `2⁻ⁿ` used to construct
the stable law. -/
theorem tendsto_charFun_stableCompensatedPoissonMeasure_invTwoPow {α β : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (t : ℝ) :
    Tendsto (fun n : ℕ ↦
      charFun (stableCompensatedPoissonMeasure α β ((2 : ℝ)⁻¹ ^ n)) t) atTop
      (𝓝 (Complex.exp (stableCharacteristicExponent α β t))) :=
  (tendsto_charFun_stableCompensatedPoissonMeasure hα hβ t).comp
    (tendsto_pow_atTop_nhdsWithin_zero_of_lt_one (by norm_num) (by norm_num))

end TauCeti.Probability
