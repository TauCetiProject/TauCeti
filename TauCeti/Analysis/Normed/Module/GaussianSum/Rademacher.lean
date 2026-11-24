/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype.Basic

import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype.Comparison
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Gaussian sums are dominated by Rademacher sums under cotype `2`

If a real normed space `Y` has Gaussian cotype `2` with constant `C` (in particular if it has
Rademacher cotype `2` with constant `C`), then the Gaussian second moment of every finite family
`y` is controlled by its Rademacher second moment:
`G₂(y) = (𝔼_g ‖∑ i, gᵢ yᵢ‖²)^(1/2) ≤ 4 √3 C R₂(y)`.

The proof applies the threshold comparison `gaussianSecondMoment_le_two_mul_rademacherSecondMoment`
at `t = 2 √3 C` together with the fourth-moment tail bound `setIntegral_sq_tail_gaussianReal_le`
(and `subsingleton_of_lt_one` when `C = 0`).

## Main declarations

* `TauCeti.HasGaussianCotype.gaussianSecondMoment_le`, `TauCeti.HasCotype.gaussianSecondMoment_le`:
  `G₂(y) ≤ 4 √3 C R₂(y)` under Gaussian or Rademacher cotype `2` with constant `C`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*, CBMS Regional
  Conference Series in Mathematics 60, AMS, 1986, §3, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped NNReal BigOperators

namespace TauCeti

variable {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι] [DecidableEq ι]
  {C : ℝ≥0}

/-- **Gaussian sums under Gaussian cotype `2`.** If `Y` has Gaussian cotype `2` with constant
`C`, the Gaussian second moment of every finite family is at most `4 √3 C` times its
Rademacher second moment: `G₂(y) ≤ 4 √3 C R₂(y)`. -/
theorem HasGaussianCotype.gaussianSecondMoment_le (h : HasGaussianCotype Y 2 C) (y : ι → Y) :
    gaussianSecondMoment y ≤ 4 * √3 * C * rademacherSecondMoment y := by
  rcases eq_or_ne C 0 with rfl | hC
  · have : Subsingleton Y := h.subsingleton_of_lt_one one_pos
    simp [Subsingleton.elim y 0]
  have : 0 < (C : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hC)
  have ht : 0 < 2 * √3 * (C : ℝ) := by positivity
  have htail :
      (C : ℝ) * √(∫ r in {r : ℝ | 2 * √3 * (C : ℝ) < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤
        1 / 2 := by
    calc
      (C : ℝ) * √(∫ r in {r : ℝ | 2 * √3 * (C : ℝ) < |r|}, r ^ 2 ∂gaussianReal 0 1)
          ≤ (C : ℝ) * √(3 / (2 * √3 * (C : ℝ)) ^ 2) := by
        gcongr
        exact setIntegral_sq_tail_gaussianReal_le ht
      _ = 1 / 2 := by
        rw [Real.sqrt_div (by norm_num), Real.sqrt_sq ht.le]
        field_simp
  simpa only [mul_assoc] using
    (gaussianSecondMoment_le_two_mul_rademacherSecondMoment h htail y).trans_eq (by ring)

/-- **Gaussian sums under cotype `2`.** If `Y` has Rademacher cotype `2` with constant `C`,
then `G₂(y) ≤ 4 √3 C R₂(y)` for every finite family `y`. -/
theorem HasCotype.gaussianSecondMoment_le (h : HasCotype Y 2 C) (y : ι → Y) :
    gaussianSecondMoment y ≤ 4 * √3 * C * rademacherSecondMoment y :=
  h.hasGaussianCotype_two.gaussianSecondMoment_le y

end TauCeti
