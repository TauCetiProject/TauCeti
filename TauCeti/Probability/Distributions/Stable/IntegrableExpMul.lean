/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.CompoundPoisson.Transforms
import TauCeti.Probability.Distributions.Stable.Operations

/-!
# One-sided exponential integrability of totally skewed stable laws

At full skewness `|β| = 1` the stable Lévy measure `stableLevyMeasure α β` charges only one
half-line: the positive one for `β = 1` and the negative one for `β = -1`. For `t` on the
opposite half-line, that is `β * t ≤ 0`, the exponential `exp (t * x)` is therefore at most one
on almost every jump, and the real compensated kernel `exp (t * x) - 1 - t * sin x` is
integrable against the Lévy measure: it vanishes quadratically at zero and is bounded on the
jumps that occur.

For such `t` the compensated compound-Poisson approximations
`stableCompensatedPoissonMeasure α β ε` have the moment generating function
`exp (∫ x in {x | ε < |x|}, exp (t * x) - 1 - t * sin x ∂ν)`. This is bounded independently of
the cutoff by `exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂ν)`, at every such `t`, in particular at
parameters of larger absolute value on the same half-line. Lower semicontinuity of integrals
under weak convergence transfers the bound to the limiting stable law. Hence every totally
skewed stable law `stableMeasure α β s m` with `|β| = 1` has finite exponential moments on the
half-line `β * t ≤ 0`, at every shape `0 < α ≤ 2`, scale, and location; the half-line condition
on the Lévy measure is `TauCeti.Probability.ae_mul_nonpos_stableLevyMeasure`, and scale and
location are handled by `TauCeti.Probability.stableMeasure_map_affine`.

## Main results

* `TauCeti.Probability.mgf_stableCompensatedPoissonMeasure`: the moment generating function of
  a compensated approximation as the exponential of a truncated compensated Lévy integral.
* `TauCeti.Probability.mgf_stableCompensatedPoissonMeasure_le`: the cutoff-independent bound.
* `TauCeti.Probability.integrable_exp_mul_stableMeasure` and
  `TauCeti.Probability.mem_integrableExpSet_id_stableMeasure`: one-sided exponential
  integrability of the stable law.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, section 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {α β ε t : ℝ}

/-- If `t * x ≤ 0` for almost every jump `x` of the stable Lévy measure, then `exp (t * x)` is
integrable under the normalized jump law, which is absolutely continuous with respect to the
Lévy measure. -/
private theorem integrable_exp_mul_cond_stableLevyMeasure
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Integrable (fun x ↦ exp (t * AddMonoidHom.id ℝ x))
      (cond (stableLevyMeasure α β) {x | ε < |x|}) := by
  by_cases h : stableLevyMeasure α β {x | ε < |x|} = ∞ ∨
      stableLevyMeasure α β {x | ε < |x|} = 0
  · rw [cond_eq_zero.mpr h]
    exact integrable_zero_measure
  have := cond_isProbabilityMeasure_of_finite (not_or.mp h).2 (not_or.mp h).1
  simpa only [one_mul, AddMonoidHom.id_apply] using integrable_exp_mul_of_le
    (X := fun x ↦ t * x) 1 0 zero_le_one (by fun_prop) (cond_absolutelyContinuous.ae_le ht)

/-- If `t * x ≤ 0` for almost every jump `x` of the stable Lévy measure, then the exponential
`exp (t * x)` is integrable under every compensated stable approximation. -/
theorem integrable_exp_mul_stableCompensatedPoissonMeasure
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Integrable (fun x ↦ exp (t * x)) (stableCompensatedPoissonMeasure α β ε) := by
  -- Translation by the sine compensator is the affine map with slope one.
  change t ∈ integrableExpSet id _
  rw [stableCompensatedPoissonMeasure_def]
  set c := ∫ y in {y : ℝ | ε < |y|}, sin y ∂stableLevyMeasure α β
  rw [show (fun x : ℝ ↦ x - c) = fun x ↦ -c + 1 * x by ext x; ring,
    integrableExpSet_id_map_affine, mem_preimage, one_mul]
  exact integrable_exp_mul_compoundPoissonMeasure _ measurable_id
    (integrable_exp_mul_cond_stableLevyMeasure ht)

/-- If `t * x ≤ 0` for almost every jump `x` of the stable Lévy measure, then the moment
generating function of a compensated stable approximation is the exponential of the truncated
compensated Lévy integral. -/
theorem mgf_stableCompensatedPoissonMeasure (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε)
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
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
      exp (∫ x in s, exp (t * x) ∂ν - ν.real s) :=
    mgf_compoundPoissonMeasure_cond (f := AddMonoidHom.id ℝ) measurable_id hm0 hm_top hexp
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
theorem mgf_stableCompensatedPoissonMeasure_le (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    mgf id (stableCompensatedPoissonMeasure α β ε) t ≤
      exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂stableLevyMeasure α β) := by
  have hi := integrable_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure ht
  rw [mgf_stableCompensatedPoissonMeasure hα hβ hε ht, exp_le_exp]
  calc
    _ ≤ ∫ x in {x : ℝ | ε < |x|}, |exp (t * x) - 1 - t * sin x| ∂stableLevyMeasure α β :=
      setIntegral_mono hi.integrableOn hi.abs.integrableOn fun x ↦ le_abs_self _
    _ ≤ _ := setIntegral_le_integral hi.abs (ae_of_all _ fun x ↦ abs_nonneg _)

/-- The standardized totally skewed stable law has finite exponential moments on the
half-line `β * t ≤ 0`, by lower semicontinuity along its compensated approximations. -/
private theorem integrable_exp_mul_stableMeasure_one_zero (hα : α ∈ Ioo 0 2) (hβ : |β| = 1)
    (ht : β * t ≤ 0) : Integrable (fun x ↦ exp (t * x)) (stableMeasure α β 1 0) := by
  have hae := ae_mul_nonpos_stableLevyMeasure (α := α) hβ ht
  have hle := le_liminf_lintegral_of_tendsto_probabilityMeasure
    (f := fun x : ℝ ↦ ENNReal.ofReal (exp (t * x)))
    (ENNReal.continuous_ofReal.comp (by fun_prop)).lowerSemicontinuous
    (tendsto_stableCompensatedPoissonMeasure_invTwoPow hα hβ.le)
  simp only [ProbabilityMeasure.coe_mk] at hle
  have hbound (n : ℕ) :
      ∫⁻ x, ENNReal.ofReal (exp (t * x))
          ∂stableCompensatedPoissonMeasure α β ((2 : ℝ)⁻¹ ^ n) ≤
        ENNReal.ofReal (exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂stableLevyMeasure α β)) := by
    have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_mul_stableCompensatedPoissonMeasure hae)
      (ae_of_all _ fun x ↦ (exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (mgf_stableCompensatedPoissonMeasure_le hα hβ.le hε hae)
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ (exp_pos _).le)).mpr
    ?_⟩
  exact hle.trans_lt ((liminf_le_of_frequently_le' (Frequently.of_forall hbound)).trans_lt
    ENNReal.ofReal_lt_top)

/-- A totally skewed stable law, `|β| = 1`, has finite exponential moments on the half-line
`β * t ≤ 0`, at every shape, scale, and location. Invalid shapes give the zero measure. -/
theorem integrable_exp_mul_stableMeasure (hβ : |β| = 1) (s : ℝ≥0) (m : ℝ) (ht : β * t ≤ 0) :
    Integrable (fun x ↦ exp (t * x)) (stableMeasure α β s m) := by
  by_cases hα : α ∈ Ioc 0 2
  swap
  · rw [stableMeasure_of_invalid (by grind)]
    exact integrable_zero_measure
  rcases hα.2.eq_or_lt with rfl | hα2
  · rw [stableMeasure_two hβ.le]
    exact integrable_exp_mul_gaussianReal t
  rcases eq_zero_or_pos s with rfl | hs
  · rw [stableMeasure_zero_scale hα hβ.le]
    exact integrable_dirac' (by fun_prop) (by simp)
  -- A positive scale and a location are an affine image of the standardized law.
  have hmap : (stableMeasure α β 1 0).map (fun x ↦ m + s * x) = stableMeasure α β s m := by
    simpa [Real.sign_of_pos (NNReal.coe_pos.mpr hs)] using
      stableMeasure_map_affine (α := α) (β := β) (s := 1) (m := 0) (a := m) (b := s)
        (Or.inl (NNReal.coe_ne_zero.mpr hs.ne'))
  change t ∈ integrableExpSet id _
  rw [← hmap, integrableExpSet_id_map_affine]
  have hts : β * (s * t) ≤ 0 := by
    rw [mul_left_comm]; exact mul_nonpos_of_nonneg_of_nonpos s.2 ht
  exact integrable_exp_mul_stableMeasure_one_zero ⟨hα.1, hα2⟩ hβ hts

/-- The half-line `β * t ≤ 0` lies in the exponential-integrability set of a totally skewed
stable law. -/
theorem mem_integrableExpSet_id_stableMeasure (hβ : |β| = 1) (s : ℝ≥0) (m : ℝ)
    (ht : β * t ≤ 0) : t ∈ integrableExpSet id (stableMeasure α β s m) :=
  integrable_exp_mul_stableMeasure hβ s m ht

end TauCeti.Probability
