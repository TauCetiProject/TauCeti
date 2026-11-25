/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Semicontinuity and measurability of the linear distortions

For fixed orientations `oV`, `oW` of real inner product spaces of the same finite dimension, the
outer distortion `q_O(A)` (`Orientation.outerDistortion`) is a lower semicontinuous function of
`A : V →L[ℝ] W`, and both `q_O` and the inner distortion `q_I` (`Orientation.innerDistortion`)
are Borel measurable.

Lower semicontinuity is all one can ask for: `q_O` is not continuous. Near a nonzero map `A` with
`J(A) ≤ 0` the outer distortion tends to `∞ = q_O(A)`, since `‖B‖` stays away from `0` while
`J(B)` is at most a small positive number; but in positive dimension `q_O(0) = 0`, while
`q_O(t A) = q_O(A)` for every `t > 0`.

## Main declarations

* `Orientation.lowerSemicontinuous_outerDistortion`: `A ↦ q_O(A)` is lower semicontinuous.
* `Orientation.measurable_outerDistortion`, `Orientation.measurable_innerDistortion`: both
  distortions are Borel measurable.
-/

public section

noncomputable section

open Module Filter Topology
open scoped ENNReal

namespace Orientation

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]
  (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))

/-- Near a nonzero map `A` with `J(A) ≤ 0`, the outer distortion exceeds every finite bound. -/
theorem eventually_lt_outerDistortion_of_nonpos {A : V →L[ℝ] W} (hA : A ≠ 0)
    (hJ : oV.orientedJacobian oW A.toLinearMap ≤ 0) {y : ℝ≥0∞} (hy : y < ⊤) :
    ∀ᶠ B : V →L[ℝ] W in 𝓝 A, y < oV.outerDistortion oW (B : V →ₗ[ℝ] W) := by
  lift y to NNReal using hy.ne
  set a := ‖A‖ / 2
  have ha0 : 0 < a := half_pos (norm_pos_iff.mpr hA)
  have hε : 0 < a ^ n / ((y : ℝ) + 1) := div_pos (pow_pos ha0 n) (by positivity)
  have hnorm : ∀ᶠ B in 𝓝 A, a < ‖B‖ :=
    continuousAt_const.eventually_lt continuous_norm.continuousAt
      (half_lt_self (norm_pos_iff.mpr hA))
  have hJB : ∀ᶠ B in 𝓝 A, oV.orientedJacobian oW B.toLinearMap < a ^ n / ((y : ℝ) + 1) :=
    (oV.continuous_orientedJacobian oW).continuousAt.eventually_lt continuousAt_const
      (hJ.trans_lt hε)
  filter_upwards [hnorm, hJB] with B hB hJB
  have hB0 : (B : V →ₗ[ℝ] W) ≠ 0 := by
    intro h
    have : B = 0 := ContinuousLinearMap.coe_injective (by simpa using h)
    rw [this, norm_zero] at hB
    exact ha0.not_ge hB.le
  by_cases hpos : 0 < oV.orientedJacobian oW B.toLinearMap
  · rw [oV.outerDistortion_of_pos oW hpos]
    rw [LinearMap.toContinuousLinearMap_coe, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_lt_ofReal_iff (div_pos (pow_pos (ha0.trans hB) n) hpos), lt_div_iff₀ hpos]
    calc (y : ℝ) * oV.orientedJacobian oW B.toLinearMap
        < ((y : ℝ) + 1) * (a ^ n / ((y : ℝ) + 1)) :=
          mul_lt_mul_of_nonneg_of_pos' (by linarith) hJB hpos.le (by positivity)
      _ = a ^ n := mul_div_cancel₀ _ (by positivity)
      _ ≤ _ := pow_le_pow_left₀ ha0.le hB.le n
  · rw [oV.outerDistortion_of_nonpos oW (not_lt.mp hpos) hB0]
    exact ENNReal.coe_lt_top

/-- **Lower semicontinuity of the outer distortion**: for fixed orientations,
`A ↦ q_O(A)` is lower semicontinuous on `V →L[ℝ] W`. -/
theorem lowerSemicontinuous_outerDistortion :
    LowerSemicontinuous fun A : V →L[ℝ] W ↦ oV.outerDistortion oW (A : V →ₗ[ℝ] W) := by
  intro A y hy
  dsimp only at hy ⊢
  by_cases hJ : 0 < oV.orientedJacobian oW A.toLinearMap
  · -- Near `A` the outer distortion is `ofReal (‖B‖ⁿ / J(B))`, continuous at `A`.
    have hcont : ContinuousAt (fun B : V →L[ℝ] W ↦
        ENNReal.ofReal (‖B‖ ^ n / oV.orientedJacobian oW B.toLinearMap)) A :=
      ENNReal.continuous_ofReal.continuousAt.comp
        (((continuous_norm.pow n).continuousAt).div
          (oV.continuous_orientedJacobian oW).continuousAt hJ.ne')
    have heq : (fun B : V →L[ℝ] W ↦
        ENNReal.ofReal (‖B‖ ^ n / oV.orientedJacobian oW B.toLinearMap)) =ᶠ[𝓝 A]
        fun B ↦ oV.outerDistortion oW (B : V →ₗ[ℝ] W) := by
      filter_upwards [continuousAt_const.eventually_lt
        (oV.continuous_orientedJacobian oW).continuousAt hJ] with B hB
      rw [oV.outerDistortion_of_pos oW hB, LinearMap.toContinuousLinearMap_coe]
    exact (hcont.congr heq).lowerSemicontinuousAt y hy
  by_cases hA : A = 0
  · subst hA
    simp only [outerDistortion_def, hJ, ite_false] at hy
    simp at hy
  rw [oV.outerDistortion_of_nonpos oW (not_lt.mp hJ)
    (fun h ↦ hA (ContinuousLinearMap.coe_injective (by simpa using h)))] at hy
  exact oV.eventually_lt_outerDistortion_of_nonpos oW hA (not_lt.mp hJ) hy

/-- The outer distortion is a Borel measurable function of `A : V →L[ℝ] W`. -/
theorem measurable_outerDistortion [MeasurableSpace (V →L[ℝ] W)]
    [OpensMeasurableSpace (V →L[ℝ] W)] :
    Measurable fun A : V →L[ℝ] W ↦ oV.outerDistortion oW (A : V →ₗ[ℝ] W) :=
  (oV.lowerSemicontinuous_outerDistortion oW).measurable

/-- The inner distortion is a Borel measurable function of `A : V →L[ℝ] W`. -/
theorem measurable_innerDistortion [FiniteDimensional ℝ W] [MeasurableSpace (V →L[ℝ] W)]
    [OpensMeasurableSpace (V →L[ℝ] W)] :
    Measurable fun A : V →L[ℝ] W ↦ oV.innerDistortion oW (A : V →ₗ[ℝ] W) := by
  have hJ := (oV.continuous_orientedJacobian oW).measurable
  simp_rw [innerDistortion_def]
  exact Measurable.ite (measurableSet_lt measurable_const hJ)
    (hJ.div (LinearMap.measurable_minimalStretch.pow_const n)) measurable_const

end Orientation
