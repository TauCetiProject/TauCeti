/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedGamma.Moments
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Exponential integrability of generalized gamma laws

The power parameter determines the exact exponential-integrability domain: the whole real
line for `c > 1`, the open half-line below the reciprocal scale for `c = 1`, and the closed
nonpositive half-line for every other nonzero `c < 1`.

For positive powers this follows by comparing the power transform of the underlying Gamma
variable with a linear function, on a bounded initial interval and on the tail separately.
For negative powers the sharp real-power moment criterion rules out positive exponential
moments. These domain results distinguish the stretched-exponential and heavy-tailed laws
from those having exponential moments of every order.

## References

* E. W. Stacy, *A Generalization of the Gamma Distribution*, Annals of Mathematical
  Statistics 33 (1962), 1187–1192. We also allow negative power parameters.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

namespace TauCeti.Probability

variable {a c s t : ℝ}

/-- Every nonpositive exponential rate is integrable, including for invalid zero laws. -/
theorem integrable_exp_mul_id_generalizedGammaMeasure_of_nonpos
    (a c s : ℝ) (ht : t ≤ 0) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (generalizedGammaMeasure a c s) :=
  integrable_exp_mul_of_ge t 0 ht measurable_id.aemeasurable
    ((ae_pos_generalizedGammaMeasure a c s).mono fun _ hx ↦ hx.le)

/-- Above power parameter one, every exponential rate is integrable, for any shape and scale. -/
theorem integrable_exp_mul_id_generalizedGammaMeasure_of_one_lt
    (hc : 1 < c) (a s t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (generalizedGammaMeasure a c s) := by
  by_cases h : 0 < a ∧ c ≠ 0 ∧ 0 < s
  swap
  · simp [generalizedGammaMeasure_of_not_valid h]
  obtain ⟨ha, hc0, hs⟩ := h
  by_cases ht : t ≤ 0
  · exact integrable_exp_mul_id_generalizedGammaMeasure_of_nonpos a c s ht
  have ht : 0 < t := lt_of_not_ge ht
  have hp : 0 < c⁻¹ := inv_pos.mpr (by linarith)
  have hp1 : c⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hc
  have hsmall : ∀ᶠ x : ℝ in atTop, t * s * x ^ (c⁻¹ - 1) < 1 / 2 := by
    have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hp1)).const_mul (t * s)
    simpa only [neg_sub, mul_zero] using (tendsto_order.1 hlim).2 (1 / 2) (by norm_num)
  obtain ⟨A, hA⟩ := eventually_atTop.1 hsmall
  rw [generalizedGammaMeasure_of_valid ha hc0 hs,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  let _ := isProbabilityMeasure_gammaMeasure ha zero_lt_one
  have hdom := (integrable_const (exp (t * s * A ^ c⁻¹))).add
    (integrable_exp_mul_id_gammaMeasure ha zero_lt_one (t := 1 / 2) (by norm_num))
  refine hdom.mono' (by fun_prop) ?_
  filter_upwards [ae_pos_gammaMeasure a 1] with x hx
  simp only [Function.comp_def, Pi.add_apply, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  by_cases hxA : x ≤ A
  · have hbound : exp (t * (s * x ^ c⁻¹)) ≤ exp (t * s * A ^ c⁻¹) := by
      apply exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_left (rpow_le_rpow hx.le hxA hp.le)
        (mul_pos ht hs).le]
    exact hbound.trans (le_add_of_nonneg_right (exp_nonneg _))
  · have htail := (hA x (le_of_not_ge hxA)).le
    rw [rpow_sub_one hx.ne', ← mul_div_assoc] at htail
    have hbound : exp (t * (s * x ^ c⁻¹)) ≤ exp ((1 / 2) * x) := by
      apply exp_le_exp.2
      have := (div_le_iff₀ hx).1 htail
      nlinarith
    exact hbound.trans (le_add_of_nonneg_left (exp_nonneg _))

private theorem not_integrable_exp_mul_id_generalizedGammaMeasure_of_pos_lt_one
    (ha : 0 < a) (hc : 0 < c) (hc1 : c < 1) (hs : 0 < s) (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ ↦ exp (t * x)) (generalizedGammaMeasure a c s) := by
  have hp1 : 1 < c⁻¹ := (one_lt_inv₀ hc).2 hc1
  have hlarge : ∀ᶠ x : ℝ in atTop, 2 / (t * s) ≤ x ^ (c⁻¹ - 1) :=
    (tendsto_rpow_atTop (sub_pos.mpr hp1)).eventually_ge_atTop _
  obtain ⟨A, hA⟩ := eventually_atTop.1 hlarge
  rw [generalizedGammaMeasure_of_valid ha hc.ne' hs,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  intro hint
  let _ := isProbabilityMeasure_gammaMeasure ha zero_lt_one
  have hdom := (integrable_const (exp (2 * A))).add hint
  have hbad : Integrable (fun x : ℝ ↦ exp (2 * x)) (gammaMeasure a 1) := by
    refine hdom.mono' (by fun_prop) ?_
    filter_upwards [ae_pos_gammaMeasure a 1] with x hx
    simp only [Function.comp_def, Pi.add_apply, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    by_cases hxA : x ≤ A
    · exact (exp_le_exp.2 (by linarith)).trans
        (le_add_of_nonneg_right (exp_nonneg _))
    · have htail := hA x (le_of_not_ge hxA)
      rw [rpow_sub_one hx.ne'] at htail
      have hlin : 2 * x ≤ t * (s * x ^ c⁻¹) := by
        have := (div_le_div_iff₀ (mul_pos ht hs) hx).1 htail
        nlinarith
      exact (exp_le_exp.2 hlin).trans (le_add_of_nonneg_left (exp_nonneg _))
  exact not_integrable_exp_mul_id_gammaMeasure ha zero_lt_one (by norm_num) hbad

/-- Below power parameter one, no positive exponential rate is integrable. This includes
negative power parameters, whose sufficiently high real-power moments already diverge. -/
theorem not_integrable_exp_mul_id_generalizedGammaMeasure_of_lt_one
    (ha : 0 < a) (hc : c ≠ 0) (hc1 : c < 1) (hs : 0 < s) (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ ↦ exp (t * x)) (generalizedGammaMeasure a c s) := by
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hq : 0 ≤ -a * c := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 ha.le) hcneg.le
    have hmom : ¬ Integrable (fun x : ℝ ↦ x ^ (-a * c))
        (generalizedGammaMeasure a c s) := by
      rw [integrable_rpow_generalizedGammaMeasure_iff ha hc hs, mul_div_cancel_right₀ _ hc]
      linarith
    exact not_integrable_exp_mul_of_not_integrable_rpow (-a * c)
      measurable_id.aemeasurable
      ((ae_pos_generalizedGammaMeasure a c s).mono fun _ hx ↦ hx.le) hq hmom ht
  · exact not_integrable_exp_mul_id_generalizedGammaMeasure_of_pos_lt_one
      ha hcpos hc1 hs ht

/-- Above power parameter one, the exponential-integrability domain is all of `ℝ`,
including for invalid zero laws. -/
@[simp]
theorem integrableExpSet_id_generalizedGammaMeasure_of_one_lt
    (hc : 1 < c) (a s : ℝ) :
    integrableExpSet id (generalizedGammaMeasure a c s) = univ := by
  ext t
  simp [integrableExpSet, integrable_exp_mul_id_generalizedGammaMeasure_of_one_lt hc a s]

/-- Below power parameter one, exponential integrability is equivalent to a nonpositive rate. -/
@[simp]
theorem integrable_exp_mul_id_generalizedGammaMeasure_iff_of_lt_one
    (ha : 0 < a) (hc : c ≠ 0) (hc1 : c < 1) (hs : 0 < s) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (generalizedGammaMeasure a c s) ↔ t ≤ 0 :=
  ⟨fun h ↦ not_lt.1 fun ht ↦
    not_integrable_exp_mul_id_generalizedGammaMeasure_of_lt_one ha hc hc1 hs ht h,
    integrable_exp_mul_id_generalizedGammaMeasure_of_nonpos a c s⟩

/-- Below power parameter one, the exponential-integrability domain is `(-∞, 0]`. -/
@[simp]
theorem integrableExpSet_id_generalizedGammaMeasure_of_lt_one
    (ha : 0 < a) (hc : c ≠ 0) (hc1 : c < 1) (hs : 0 < s) :
    integrableExpSet id (generalizedGammaMeasure a c s) = Iic 0 := by
  ext t
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq, mem_Iic] using
    integrable_exp_mul_id_generalizedGammaMeasure_iff_of_lt_one ha hc hc1 hs t

/-- At power parameter one, the exponential-integrability domain excludes the reciprocal scale.
For `simp`, `generalizedGammaMeasure_one` reduces this to the Gamma domain theorem. -/
theorem integrableExpSet_id_generalizedGammaMeasure_one (ha : 0 < a) (hs : 0 < s) :
    integrableExpSet id (generalizedGammaMeasure a 1 s) = Iio s⁻¹ := by
  rw [generalizedGammaMeasure_one ha hs, integrableExpSet_id_gammaMeasure ha (inv_pos.2 hs)]

/-- At power parameter one, exponential integrability holds exactly below the reciprocal scale. -/
theorem integrable_exp_mul_id_generalizedGammaMeasure_one_iff
    (ha : 0 < a) (hs : 0 < s) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (generalizedGammaMeasure a 1 s) ↔ t < s⁻¹ := by
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq, mem_Iio] using
    Set.ext_iff.1 (integrableExpSet_id_generalizedGammaMeasure_one ha hs) t

/-- The exact exponential-integrability domain of a valid generalized gamma law.
At power one the endpoint is excluded; below power one the endpoint zero is included. -/
@[simp]
theorem integrableExpSet_id_generalizedGammaMeasure
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    integrableExpSet id (generalizedGammaMeasure a c s) =
      if 1 < c then univ else if c = 1 then Iio s⁻¹ else Iic 0 := by
  rcases lt_trichotomy c 1 with hc1 | rfl | hc1
  · simpa only [not_lt.mpr hc1.le, ↓reduceIte, hc1.ne] using
      integrableExpSet_id_generalizedGammaMeasure_of_lt_one ha hc hc1 hs
  · simpa only [lt_self_iff_false, ↓reduceIte] using
      integrableExpSet_id_generalizedGammaMeasure_one ha hs
  · simpa only [hc1, ↓reduceIte] using
      integrableExpSet_id_generalizedGammaMeasure_of_one_lt hc1 a s

end TauCeti.Probability
