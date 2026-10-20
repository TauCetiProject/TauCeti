/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Levy.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.InverseGamma.Moments

/-!
# Moment thresholds of the Lévy distribution

A Lévy variable `X` with location `m` and positive scale is heavy-tailed: its density decays like
`(x - m) ^ (-3 / 2)`. The real power `|X - m| ^ q` is integrable exactly when `q < 1 / 2`, so in
particular `X` has no mean. Its exponential moments `E[exp (t X)]` exist exactly for `t ≤ 0`.

Both facts are transported from the inverse-gamma law of shape `1 / 2`, which is the law of
`X - m`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {m c : ℝ}

/-- **The moment threshold of the Lévy law.** For a Lévy law with location `m` and positive scale,
the real power `|x - m| ^ q` is integrable exactly when `q < 1 / 2`. -/
@[simp]
theorem integrable_rpow_abs_sub_levyMeasure_iff (hc : 0 < c) (m q : ℝ) :
    Integrable (fun x : ℝ ↦ |x - m| ^ q) (levyMeasure m c) ↔ q < 1 / 2 := by
  have hcongr : (fun y : ℝ ↦ |m + y - m| ^ q) =ᵐ[inverseGammaMeasure (1 / 2) (c / 2)]
      fun y ↦ y ^ q := by
    filter_upwards [ae_pos_inverseGammaMeasure (1 / 2) (c / 2)] with y hy
    rw [add_sub_cancel_left, abs_of_pos hy]
  rw [levyMeasure_def, integrable_map_measure
      (by fun_prop : Measurable fun x : ℝ ↦ |x - m| ^ q).aestronglyMeasurable
      (measurable_const_add m).aemeasurable,
    Function.comp_def, integrable_congr hcongr,
    integrable_rpow_inverseGammaMeasure_iff one_half_pos (half_pos hc)]

/-- **A Lévy law has no mean.** -/
theorem not_integrable_id_levyMeasure (hc : 0 < c) (m : ℝ) :
    ¬ Integrable id (levyMeasure m c) := by
  intro h
  let _ := isProbabilityMeasure_levyMeasure hc m
  have habs : Integrable (fun x : ℝ ↦ |x - m| ^ (1 : ℝ)) (levyMeasure m c) := by
    have hsub : Integrable (fun x : ℝ ↦ x - m) (levyMeasure m c) := h.sub (integrable_const m)
    simpa only [Real.rpow_one] using hsub.abs
  have hlt := (integrable_rpow_abs_sub_levyMeasure_iff hc m 1).mp habs
  norm_num at hlt

/-- **The exact exponential-integrability domain of a Lévy law** with positive scale is the
nonpositive half-line. -/
@[simp]
theorem integrableExpSet_id_levyMeasure (hc : 0 < c) (m : ℝ) :
    integrableExpSet id (levyMeasure m c) = Iic 0 := by
  rw [levyMeasure_eq_map_affine_levyMeasure_zero_one hc, integrableExpSet_id_map_affine,
    levyMeasure_zero_left, integrableExpSet_id_inverseGammaMeasure one_half_pos one_half_pos]
  ext t
  simp only [mem_preimage, mem_Iic]
  constructor <;> intro h <;> nlinarith

end Probability

end TauCeti
