/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Additive Haar measures on Euclidean space and Lebesgue measure on `ι → ℝ`

Every additive Haar measure `μ` on `EuclideanSpace ℝ ι` is a positive finite multiple `a • volume`
of the volume measure, and `ofLp` carries the volume measure to Lebesgue measure on `ι → ℝ`. So
`ofLp` carries `μ` to `a • volume`, and `μ` gives the preimage under `ofLp` of a set `S ⊆ ι → ℝ`
the measure `a * volume S`. In particular a cube, the preimage of a sup-norm closed ball, can be
compared with the concentric Euclidean ball: the cube of half-side `r` has measure at most `√nⁿ`
times that of the Euclidean ball of radius `r`, since that ball contains the cube of half-side
`r / √n`.

## Main results

* `EuclideanSpace.exists_map_toLp_symm_eq_smul`: an additive Haar measure is carried by `ofLp` to
  a positive finite multiple of Lebesgue measure.
* `EuclideanSpace.measure_preimage_ofLp`: the measure of a preimage under `ofLp`.
* `EuclideanSpace.measure_preimage_ofLp_closedBall_le`: a cube has measure at most `√nⁿ` times
  that of the Euclidean ball of the same radius.
-/

public section

open MeasureTheory Metric WithLp
open scoped ENNReal

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι]

/-- An additive Haar measure on `EuclideanSpace ℝ ι` is carried by `ofLp` to a positive finite
multiple of Lebesgue measure on `ι → ℝ`. -/
theorem exists_map_toLp_symm_eq_smul (μ : Measure (EuclideanSpace ℝ ι)) [μ.IsAddHaarMeasure] :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ⊤ ∧ μ.map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm = a • volume := by
  refine ⟨Measure.addHaarScalarFactor μ volume, ENNReal.coe_ne_zero.2
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne', ENNReal.coe_ne_top, ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ volume]
  rw [Measure.map_smul, (volume_preserving_symm_measurableEquiv_toLp ι).map_eq,
    Measure.coe_nnreal_smul]
  exact (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable.aemeasurable

/-- If `ofLp` carries `μ` to `a • volume`, then `μ` gives the preimage of `S` the measure
`a * volume S`. -/
theorem measure_preimage_ofLp {μ : Measure (EuclideanSpace ℝ ι)} {a : ℝ≥0∞}
    (he : μ.map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm = a • volume) (S : Set (ι → ℝ)) :
    μ (ofLp ⁻¹' S) = a * volume S := by
  rw [← MeasurableEquiv.coe_toLp_symm, ← MeasurableEquiv.map_apply, he, Measure.smul_apply,
    smul_eq_mul]

/-- The Euclidean ball `B(x, r)` lies in the cube of half-side `r` centred at `x`, whose measure
is at most `√nⁿ` times that of the ball. -/
theorem measure_preimage_ofLp_closedBall_le [Nonempty ι] (μ : Measure (EuclideanSpace ℝ ι))
    [μ.IsAddHaarMeasure] (x : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
    μ (ofLp ⁻¹' closedBall (ofLp x) r) ≤
      ENNReal.ofReal (√(Fintype.card ι) ^ Fintype.card ι) * μ (ball x r) := by
  obtain ⟨a, -, -, he⟩ := exists_map_toLp_symm_eq_smul μ
  have hs : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  -- The ball contains the cube of half-side `r / √n`.
  have hsub : ofLp ⁻¹' ball (ofLp x) (r / √(Fintype.card ι)) ⊆ ball x r := by
    convert preimage_ofLp_ball_subset_ball x (r / √(Fintype.card ι)) using 2
    field_simp
  refine le_trans (le_of_eq ?_) (mul_le_mul_right (measure_mono hsub) _)
  rw [measure_preimage_ofLp he, measure_preimage_ofLp he, Real.volume_pi_closedBall _ hr.le,
    Real.volume_pi_ball _ (by positivity), mul_left_comm, ← ENNReal.ofReal_mul (by positivity),
    ← mul_pow]
  congr 3
  field_simp

end EuclideanSpace
