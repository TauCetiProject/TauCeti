/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Volume of the closed unit ball in the mixed space

For a number field `K` of signature `(r₁, r₂)`, the open product of unit discs
`NumberField.mixedEmbedding.convexBodyLT K 1` lies inside `Metric.closedBall (0 : mixedSpace K) 1`
and has volume `2 ^ r₁ * π ^ r₂`. Using `2 ≤ π` yields the signature lower bound
`2 ^ r₁ * 2 ^ r₂ ≤ volume.real (Metric.closedBall (0 : mixedSpace K) 1)`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.two_pow_mul_two_pow_le_volume_real_closedBall`:
  `2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K` is at most
  `volume.real (Metric.closedBall (0 : mixedSpace K) 1)`.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

open scoped Classical in
/-- The real volume of the closed unit ball of `mixedSpace K` is at least `2 ^ r₁ * 2 ^ r₂`,
where `(r₁, r₂)` is the signature of `K`. -/
theorem two_pow_mul_two_pow_le_volume_real_closedBall (K : Type*) [Field K] [NumberField K] :
    (2 : ℝ) ^ nrRealPlaces K * 2 ^ nrComplexPlaces K ≤
      volume.real (Metric.closedBall (0 : mixedSpace K) 1) := by
  have hsub : convexBodyLT K 1 ⊆ Metric.closedBall (0 : mixedSpace K) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    simp only [convexBodyLT, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
      Metric.mem_ball, dist_zero_right, Pi.one_apply, NNReal.coe_one] at hz
    exact max_le ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w ↦ (hz.1 w).le)
      ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w ↦ (hz.2 w).le)
  have hfin : volume (Metric.closedBall (0 : mixedSpace K) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : mixedSpace K) 1).measure_lt_top.ne
  calc (2 : ℝ) ^ nrRealPlaces K * 2 ^ nrComplexPlaces K
      ≤ (convexBodyLTFactor K : ℝ) := by
        simp only [convexBodyLTFactor, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat,
          NNReal.coe_real_pi]
        gcongr
        exact Real.two_le_pi
    _ = volume.real (convexBodyLT K 1) := by simp [measureReal_def, convexBodyLT_volume]
    _ ≤ volume.real (Metric.closedBall (0 : mixedSpace K) 1) := measureReal_mono hsub hfin

end TauCeti.NumberField.mixedEmbedding
