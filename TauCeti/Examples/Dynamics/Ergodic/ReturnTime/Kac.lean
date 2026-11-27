/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.ReturnTime
public import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Count
import TauCeti.Dynamics.Ergodic.IsomorphicModNull
import TauCeti.Examples.Dynamics.Ergodic.ReturnTime

/-!
# Checks for Kac's lemma

Checks for `TauCeti.kac_return_time_integral` (GeometryOfNumbersAndQuadraticArithmetic §4.2,
*Kac return times*).

* On a probability singleton with `T = id` and `A = univ`, every positive return time is `1` and
  its integral is `1`.
* On the fair two-point flip `not` of `Bool` with `A = {false}`, the return time on `A` is `2`,
  the flip is ergodic, so Kac's lemma gives the unnormalized integral `1`; the conditional mean
  on `A` is `2 = 1 / μ A`.
* For the identity on two equiprobable points and `A = {false}`, the integral is `1 / 2`: this
  map is not ergodic, so the hypothesis of Kac's lemma fails. For `A = ∅` the integral is `0`, so
  positive measure is essential.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Examples.Kac

/-- **Check.** On a probability singleton, under the identity every point returns to `univ` at
time `1`, and the integral of the return time over `univ` is `1`. -/
theorem integral_positiveReturnTime_id_unit :
    (∀ x : Unit, positiveReturnTime id univ x = 1) ∧
      ∫ x in univ, ((positiveReturnTime id (univ : Set Unit) x).toNat : ℝ)
        ∂(Measure.dirac ()) = 1 := by
  have h (x : Unit) : positiveReturnTime id univ x = 1 :=
    ReturnTime.positiveReturnTime_id (mem_univ x)
  refine ⟨h, ?_⟩
  simp [h]

/-- The fair coin on `Bool`: each point has mass `1 / 2`. -/
noncomputable abbrev fairCoin : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • Measure.count

instance instIsProbabilityMeasureFairCoin : IsProbabilityMeasure fairCoin :=
  ⟨by
    rw [fairCoin, smul_apply, Measure.count_univ]
    simp [ENNReal.inv_mul_cancel]⟩

/-- Each point has mass `1 / 2` under the fair coin. -/
theorem fairCoin_singleton (b : Bool) : fairCoin {b} = 2⁻¹ := by
  simp [fairCoin]

/-- The flip `not` of `Bool` as a measurable equivalence. -/
@[expose]
def boolFlip : Bool ≃ᵐ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not
  measurable_toFun := measurable_from_top
  measurable_invFun := measurable_from_top

/-- The flip is ergodic for the fair coin. -/
theorem ergodic_boolFlip : Ergodic boolFlip fairCoin :=
  ergodic_not_count.smul_measure _

/-- **Check.** For the fair flip and `A = {false}`, the return time on `A` is `2`, and by Kac's
lemma its unnormalized integral is `1`. -/
theorem integral_positiveReturnTime_boolFlip :
    positiveReturnTime boolFlip {false} false = 2 ∧
      ∫ x in {false}, ((positiveReturnTime boolFlip {false} x).toNat : ℝ) ∂fairCoin = 1 :=
  ⟨ReturnTime.positiveReturnTime_not_false,
    (kac_return_time_integral ergodic_boolFlip (measurableSet_singleton false)
      (by simp)).2.2⟩

/-- **Check.** For the fair flip and `A = {false}`, the mean return time for the conditional
probability on `A` is `2 = 1 / μ A`. -/
theorem integral_cond_positiveReturnTime_boolFlip :
    ∫ x, ((positiveReturnTime boolFlip {false} x).toNat : ℝ) ∂(fairCoin[|{false}]) = 2 := by
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_positiveReturnTime_boolFlip.2,
    fairCoin_singleton]
  simp

/-- **Check.** For the identity on two equiprobable points and `A = {false}`, the integral of the
return time over `A` is `1 / 2`, not `1`: the identity is not ergodic. -/
theorem integral_positiveReturnTime_id_bool :
    ∫ x in {false}, ((positiveReturnTime id ({false} : Set Bool) x).toNat : ℝ) ∂fairCoin =
      1 / 2 ∧ ¬ Ergodic id fairCoin := by
  refine ⟨?_, fun h ↦ not_ergodic_id_count ?_⟩
  · rw [integral_singleton, ReturnTime.positiveReturnTime_id rfl, measureReal_def,
      fairCoin_singleton]
    simp
  · simpa [fairCoin, smul_smul, ENNReal.mul_inv_cancel] using h.smul_measure (2 : ℝ≥0∞)

/-- **Check.** For `A = ∅` the integral of the return time over `A` is `0`, so positive measure is
essential in Kac's lemma. -/
theorem integral_positiveReturnTime_empty {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X → X) : ∫ x in (∅ : Set X), ((positiveReturnTime T ∅ x).toNat : ℝ) ∂μ = 0 := by
  simp

end TauCeti.Examples.Kac
