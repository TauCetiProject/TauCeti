/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic
public import TauCeti.Probability.Distributions.Stable.LevyKhintchine
public import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.CompoundPoisson.Transforms

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

When the Lévy measure is carried by `{x | t * x ≤ 0}`, the exponential `exp (t * x)` is
integrable under every approximation, and the moment generating function at `t` is the
exponential of the real truncated compensated Lévy integral
`∫ x in {x | ε < |x|}, exp (t * x) - 1 - t * sin x ∂ν`. It is bounded independently of the
cutoff by `exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂ν)`.

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

/-- If `t * x ≤ 0` for almost every jump `x` of the stable Lévy measure, then `exp (t * x)` is
integrable under the normalized jump law, which is absolutely continuous with respect to the
Lévy measure. -/
private theorem integrable_exp_mul_cond_stableLevyMeasure {α β ε t : ℝ}
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Integrable (fun x ↦ exp (t * AddMonoidHom.id ℝ x))
      (cond (stableLevyMeasure α β) {x | ε < |x|}) := by
  simpa only [one_mul, AddMonoidHom.id_apply] using integrable_exp_mul_of_le
    (X := fun x ↦ t * x) 1 0 zero_le_one (by fun_prop) (cond_absolutelyContinuous.ae_le ht)

/-- If `t * x ≤ 0` for almost every jump `x` of the stable Lévy measure, then the exponential
`exp (t * x)` is integrable under every compensated stable approximation. -/
theorem integrable_exp_mul_stableCompensatedPoissonMeasure {α β ε t : ℝ}
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Integrable (fun x ↦ exp (t * x)) (stableCompensatedPoissonMeasure α β ε) := by
  -- Translation by the sine compensator is the affine map with slope one.
  suffices h : t ∈ integrableExpSet id (stableCompensatedPoissonMeasure α β ε) by
    simpa only [integrableExpSet, mem_ofPred_eq, id_eq] using h
  rw [stableCompensatedPoissonMeasure_def]
  set c := ∫ y in {y : ℝ | ε < |y|}, sin y ∂stableLevyMeasure α β
  rw [show (fun x : ℝ ↦ x - c) = fun x ↦ -c + 1 * x by ext x; ring,
    integrableExpSet_id_map_affine, mem_preimage, one_mul]
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq, AddMonoidHom.id_apply] using
    integrable_exp_mul_compoundPoissonMeasure (f := AddMonoidHom.id ℝ) _
      (by simpa only [AddMonoidHom.coe_id] using measurable_id)
      (integrable_exp_mul_cond_stableLevyMeasure ht)

/-- If `t * x ≤ 0` for almost every jump `x` of the stable Lévy measure, then the moment
generating function of a compensated stable approximation is the exponential of the truncated
compensated Lévy integral. -/
theorem mgf_stableCompensatedPoissonMeasure {α β ε t : ℝ} (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    mgf id (stableCompensatedPoissonMeasure α β ε) t =
      exp (∫ x in {x : ℝ | ε < |x|}, exp (t * x) - 1 - t * sin x ∂stableLevyMeasure α β) := by
  set ν := stableLevyMeasure α β
  set s : Set ℝ := {x | ε < |x|}
  have hm0 : ν s ≠ 0 := (stableLevyMeasure_abs_gt_pos hα hβ hε).ne'
  have hm_top : ν s ≠ ∞ := stableLevyMeasure_abs_gt_ne_top hε
  have := isFiniteMeasure_stableLevyMeasure_restrict_abs_gt (α := α) (β := β) hε
  have hexp : IntegrableOn (fun x ↦ exp (t * x)) s ν := by
    simpa only [IntegrableOn, one_mul] using integrable_exp_mul_of_le
      (X := fun x ↦ t * x) 1 0 zero_le_one (by fun_prop) (ae_restrict_of_ae ht)
  have hsin : IntegrableOn (fun x ↦ t * sin x) s ν :=
    Integrable.of_bound (by fun_prop) |t| (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg t) (abs_sin_le_one x))
  have hone : IntegrableOn (fun _ ↦ (1 : ℝ)) s ν := integrableOn_const hm_top
  -- The compound-Poisson factor, with the normalized jump law written against `ν`.
  have hcp : mgf id (compoundPoissonMeasure (ν s).toNNReal (cond ν s)) t =
      exp (∫ x in s, exp (t * x) ∂ν - ν.real s) := by
    simpa only [AddMonoidHom.coe_id, AddMonoidHom.id_apply] using
      mgf_compoundPoissonMeasure_cond (f := AddMonoidHom.id ℝ)
        (by simpa only [AddMonoidHom.coe_id] using measurable_id) hm0 hm_top
        (by simpa only [AddMonoidHom.id_apply] using hexp)
  -- Split the compensated integral into its exponential, constant and sine parts.
  have hsplit : ∫ x in s, exp (t * x) - 1 - t * sin x ∂ν =
      ∫ x in s, exp (t * x) ∂ν - ν.real s - t * ∫ y in s, sin y ∂ν := by
    have hsub₁ := integral_sub (hexp.sub hone) hsin
    have hsub₂ := integral_sub hexp hone
    simp only [Pi.sub_apply] at hsub₁ hsub₂
    simp [hsub₁, hsub₂, integral_const_mul]
  -- Translation by the sine compensator contributes the factor `exp (-(t * c))`.
  rw [stableCompensatedPoissonMeasure_def, mgf_id_map (by fun_prop)]
  conv_lhs => simp only [sub_eq_add_neg]
  rw [mgf_add_const, ← Function.id_def, hcp, ← exp_add, hsplit]
  congr 1
  ring

/-- If `t * x ≤ 0` for almost every jump `x` of the stable Lévy measure, then the moment
generating functions of the compensated stable approximations are bounded independently of the
cutoff. -/
theorem mgf_stableCompensatedPoissonMeasure_le {α β ε t : ℝ} (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) (hε : 0 < ε) (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    mgf id (stableCompensatedPoissonMeasure α β ε) t ≤
      exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂stableLevyMeasure α β) := by
  have hi := integrable_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure ht
  rw [mgf_stableCompensatedPoissonMeasure hα hβ hε ht, exp_le_exp]
  calc
    _ ≤ ∫ x in {x : ℝ | ε < |x|}, |exp (t * x) - 1 - t * sin x| ∂stableLevyMeasure α β :=
      setIntegral_mono hi.integrableOn hi.abs.integrableOn fun x ↦ le_abs_self _
    _ ≤ _ := setIntegral_le_integral hi.abs (ae_of_all _ fun x ↦ abs_nonneg _)

end TauCeti.Probability
