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
import TauCeti.Probability.Distributions.Stable.Operations

/-!
# One-sided exponential integrability of totally skewed stable laws

At full skewness `|β| = 1` the stable Lévy measure `stableLevyMeasure α β` charges only one
half-line: the positive one for `β = 1` and the negative one for `β = -1`. For `t` on the
opposite half-line, that is `β * t ≤ 0`, the exponential `exp (t * x)` is therefore at most one
on almost every jump, and the real compensated kernel `exp (t * x) - 1 - t * sin x` is
integrable against the Lévy measure: it vanishes quadratically at zero and is bounded on the
jumps that occur.

For such `t` the moment generating functions of the compensated compound-Poisson
approximations `stableCompensatedPoissonMeasure α β ε` are bounded independently of the cutoff
by `exp (∫ x, |exp (t * x) - 1 - t * sin x| ∂ν)`, at every such `t`, in particular at parameters
of larger absolute value on the same half-line; this is
`TauCeti.Probability.mgf_stableCompensatedPoissonMeasure_le`. Lower semicontinuity of integrals
under weak convergence transfers the bound to the limiting stable law. Hence every totally
skewed stable law `stableMeasure α β s m` with `|β| = 1` has finite exponential moments on the
half-line `β * t ≤ 0`, at every shape `0 < α ≤ 2`, scale, and location; the half-line condition
on the Lévy measure is `TauCeti.Probability.ae_mul_nonpos_stableLevyMeasure`, and scale and
location are handled by `TauCeti.Probability.stableMeasure_map_affine`.

## Main results

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

/-- For positive scale, exponential integrability at `t` is equivalent to exponential
integrability at `s * t` for the scale-one, location-zero stable law. -/
theorem mem_integrableExpSet_id_stableMeasure_iff_one_zero {s : ℝ≥0} {m : ℝ}
    (hs : 0 < s) :
    t ∈ integrableExpSet id (stableMeasure α β s m) ↔
      (s : ℝ) * t ∈ integrableExpSet id (stableMeasure α β 1 0) := by
  have hmap : (stableMeasure α β 1 0).map (fun x ↦ m + s * x) =
      stableMeasure α β s m := by
    simpa [Real.sign_of_pos (NNReal.coe_pos.mpr hs)] using
      stableMeasure_map_affine (α := α) (β := β) (s := 1) (m := 0) (a := m) (b := s)
        (Or.inl (NNReal.coe_ne_zero.mpr hs.ne'))
  rw [← hmap, integrableExpSet_id_map_affine, mem_preimage]

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
  suffices h : t ∈ integrableExpSet id (stableMeasure α β s m) by
    simpa only [integrableExpSet, mem_ofPred_eq, id_eq] using h
  rw [mem_integrableExpSet_id_stableMeasure_iff_one_zero hs]
  have hts : β * (s * t) ≤ 0 := by
    rw [mul_left_comm]; exact mul_nonpos_of_nonneg_of_nonpos s.2 ht
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq] using
    integrable_exp_mul_stableMeasure_one_zero ⟨hα.1, hα2⟩ hβ hts

/-- The half-line `β * t ≤ 0` lies in the exponential-integrability set of a totally skewed
stable law. -/
theorem mem_integrableExpSet_id_stableMeasure (hβ : |β| = 1) (s : ℝ≥0) (m : ℝ)
    (ht : β * t ≤ 0) : t ∈ integrableExpSet id (stableMeasure α β s m) := by
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq] using
    integrable_exp_mul_stableMeasure hβ s m ht

end TauCeti.Probability
