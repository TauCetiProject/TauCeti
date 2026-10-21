/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGamma.Moments
public import TauCeti.Probability.Distributions.Levy.Basic

/-!
# Moments and exponential domain of the Lévy distribution

A Lévy variable `X` with location `m` and scale `c > 0` has `|X - m| ^ q` integrable exactly for
`q < 1 / 2`, with `E[|X - m| ^ q] = (c / 2) ^ q Γ(1 / 2 - q) / √π`; in particular it has no
mean. Its exponential moments `E[exp (t X)]` exist exactly for `t ≤ 0`.

These facts are transported from the inverse-gamma law of shape `1 / 2` and scale `c / 2`, which is
the law of `X - m`.

## Main declarations

* `TauCeti.Probability.integrable_rpow_abs_sub_levyMeasure_iff` — the sharp moment threshold;
* `TauCeti.Probability.integral_rpow_abs_sub_levyMeasure` — the absolute central moments;
* `TauCeti.Probability.integrableExpSet_id_levyMeasure` — the exponential-integrability domain.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti

namespace Probability

variable {m c q : ℝ}

/-- Under a valid inverse-gamma law, `|(m + y) - m| ^ q` agrees almost everywhere with `y ^ q`. -/
private lemma rpow_abs_add_sub_ae_eq_inverseGammaMeasure (a r m q : ℝ) :
    (fun y : ℝ ↦ |m + y - m| ^ q) =ᵐ[inverseGammaMeasure a r] fun y ↦ y ^ q := by
  filter_upwards [ae_pos_inverseGammaMeasure a r] with y hy
  rw [add_sub_cancel_left, abs_of_pos hy]

/-- The absolute central power `|x - m| ^ q` is measurable. -/
private lemma measurable_rpow_abs_sub (m q : ℝ) : Measurable fun x : ℝ ↦ |x - m| ^ q := by
  fun_prop

/-- **Sharp moment threshold of the Lévy law.** At positive scale, `|x - m| ^ q` is integrable
under the Lévy law with location `m` exactly when `q < 1 / 2`. -/
@[simp]
theorem integrable_rpow_abs_sub_levyMeasure_iff (hc : 0 < c) (m q : ℝ) :
    Integrable (fun x ↦ |x - m| ^ q) (levyMeasure m c) ↔ q < 1 / 2 := by
  rw [levyMeasure_def, integrable_map_measure (measurable_rpow_abs_sub m q).aestronglyMeasurable
    (by fun_prop), Function.comp_def,
    integrable_congr (rpow_abs_add_sub_ae_eq_inverseGammaMeasure _ _ m q),
    integrable_rpow_inverseGammaMeasure_iff one_half_pos (half_pos hc)]

/-- **Absolute central moments of the Lévy law.** For `q < 1 / 2`,
`E[|X - m| ^ q] = (c / 2) ^ q Γ(1 / 2 - q) / √π`. -/
theorem integral_rpow_abs_sub_levyMeasure (hc : 0 < c) (m : ℝ) (hq : q < 1 / 2) :
    ∫ x, |x - m| ^ q ∂levyMeasure m c = (c / 2) ^ q * Real.Gamma (1 / 2 - q) / √π := by
  rw [levyMeasure_def,
    integral_map (by fun_prop) (measurable_rpow_abs_sub m q).aestronglyMeasurable,
    integral_congr_ae (rpow_abs_add_sub_ae_eq_inverseGammaMeasure _ _ m q),
    integral_rpow_inverseGammaMeasure one_half_pos (half_pos hc) hq, Real.Gamma_one_half_eq]

/-- A Lévy law of positive scale has no mean. -/
theorem not_integrable_id_levyMeasure (hc : 0 < c) (m : ℝ) :
    ¬ Integrable id (levyMeasure m c) := by
  let _ := isProbabilityMeasure_levyMeasure hc m
  intro h
  have hsub : Integrable (fun x : ℝ ↦ x - m) (levyMeasure m c) := h.sub (integrable_const m)
  have habs : Integrable (fun x ↦ |x - m| ^ (1 : ℝ)) (levyMeasure m c) := by
    simpa only [Real.rpow_one] using hsub.abs
  exact absurd ((integrable_rpow_abs_sub_levyMeasure_iff hc m 1).mp habs) (by norm_num)

/-- **The exact exponential-integrability domain of a Lévy law** of positive scale is the
nonpositive half-line. -/
@[simp]
theorem integrableExpSet_id_levyMeasure (hc : 0 < c) (m : ℝ) :
    integrableExpSet id (levyMeasure m c) = Iic 0 := by
  have htrans : (m + · : ℝ → ℝ) = fun y ↦ m + 1 * y := by
    ext y
    rw [one_mul]
  rw [levyMeasure_def, htrans, integrableExpSet_id_map_affine,
    integrableExpSet_id_inverseGammaMeasure one_half_pos (half_pos hc)]
  ext t
  simp

end Probability

end TauCeti
