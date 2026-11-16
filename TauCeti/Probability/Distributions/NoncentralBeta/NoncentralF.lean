/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NoncentralBeta.Basic
public import TauCeti.Probability.Distributions.NoncentralF.Basic

/-!
# Noncentral Beta and noncentral F laws

If `X = U / (U + V)` has the noncentral Beta law with positive shapes `a` and `b`, then
`X / (1 - X) = U / V`, so `(b / a) * X / (1 - X)` is the variance ratio
`(U / (2 * a)) / (V / (2 * b))`, which has the noncentral F law with degrees `2 * a` and `2 * b`
and the same noncentrality.

The measure identity is accompanied by `HasLaw.mul_div_one_sub_noncentralBetaMeasure`, so the
relationship can be applied directly to a random variable with the noncentral Beta law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {a b : ℝ}

/-- For positive shapes, the noncentral F law with degrees `2 * a` and `2 * b` is the image of the
noncentral Beta law with shapes `a` and `b` under `x ↦ (b / a) * x / (1 - x)`, with the same
noncentrality. -/
theorem noncentralFMeasure_eq_map_noncentralBetaMeasure (ha : 0 < a) (hb : 0 < b) (l : ℝ≥0) :
    noncentralFMeasure (2 * a) (2 * b) l =
      (noncentralBetaMeasure a b l).map (fun x ↦ b / a * (x / (1 - x))) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure (mul_pos two_pos hb).le
  rw [noncentralFMeasure_eq_map (by positivity) (by positivity),
    noncentralBetaMeasure_eq_map hb, Measure.map_map (by fun_prop) (by fun_prop)]
  refine Measure.map_congr ?_
  filter_upwards [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ici.prod measurableSet_Ioi)
    |>.2 ((ae_nonneg_noncentralChiSquaredMeasure (2 * a) l).mono fun u hu ↦
      (ae_pos_chiSquaredMeasure (by positivity : (0 : ℝ) < 2 * b)).mono fun v hv ↦
        ⟨hu, hv⟩)] with z hz
  have hu : 0 ≤ z.1 := hz.1
  have hv : 0 < z.2 := hz.2
  have huv : z.1 + z.2 ≠ 0 := by positivity
  simp only [Function.comp_apply]
  rw [one_sub_div huv, add_sub_cancel_left, div_div_div_cancel_right₀ huv]
  field_simp

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- If `X` has a noncentral Beta law with positive first shape `a`, then
`(b / a) * X / (1 - X)` has the noncentral F law with degrees `2 * a` and `2 * b` and the same
noncentrality. For nonpositive `b`, the source law and target law are both zero, so the statement
also respects the families' totalizations outside their probability ranges. -/
theorem HasLaw.mul_div_one_sub_noncentralBetaMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {a b : ℝ} {l : ℝ≥0}
    (hX : HasLaw X (noncentralBetaMeasure a b l) P) (ha : 0 < a) :
    HasLaw (fun ω ↦ b / a * (X ω / (1 - X ω)))
      (noncentralFMeasure (2 * a) (2 * b) l) P := by
  by_cases hb : 0 < b
  · rw [noncentralFMeasure_eq_map_noncentralBetaMeasure ha hb]
    exact (hasLaw_map (P := noncentralBetaMeasure a b l)
      (X := fun x : ℝ ↦ b / a * (x / (1 - x))) (by fun_prop)).fun_comp hX
  · have hP : P = 0 := by
      rw [← Measure.map_eq_zero_iff hX.aemeasurable, hX.map_eq,
        noncentralBetaMeasure_of_not (fun h ↦ hb h.2)]
    subst P
    rw [noncentralFMeasure_of_not_pos (by simp [hb])]
    exact ⟨aemeasurable_zero_measure, Measure.map_zero _⟩

end ProbabilityTheory
