/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.NumberTheory.Hypergeometric.Zigzag
public import TauCeti.NumberTheory.Hypergeometric.HodgeVector
import Mathlib.Tactic.NormNum

/-!
# Examples of the weight and the Hodge vector

* The Legendre pair `α = (1/2, 1/2)`, `β = (1, 1)`: the two copies of `1/2` are recorded at the
  heights `0` and `1`, so the weight is `1` and the Hodge vector is `(1, 1)`. Recording both
  copies at `Z(1/2) - 1 = 1` would give weight `0` and Hodge vector `(2)`.
* The pair `α = (1/2, 1/2)`, `β = (1/4, 3/4)`: the copies of `1/2` are recorded at `-1` and `0`,
  so the least recorded height is `-1`, the weight is `1` and the Hodge vector is `(1, 1)`.
* For a pair of degree `0` the weight is `0` and the Hodge vector is `(0)`.
-/

public section

open TauCeti.Hypergeometric Set

namespace TauCeti.Hypergeometric.Examples

private theorem rep_half : rep ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 1 / 2 :=
  rep_coe_of_mem (by norm_num)

/-- The weight and the Hodge vector of a pair of positive degree whose recorded heights are
`{m, m + 1}`. -/
private theorem weight_hodgeVector_of_recordedHeights {P : Parameters} {m : ℤ}
    (hP : P.recordedHeights = {m, m + 1}) :
    P.minHeight = m ∧ P.weight = 1 ∧ P.hodgeVector = [1, 1] := by
  have hd : 0 < P.degree := by
    rw [← P.card_recordedHeights, hP]
    simp
  have hmin : P.minHeight = m :=
    (P.isLeast_minHeight hd).unique ⟨by simp [hP], by simp [hP, lowerBounds]⟩
  have hmax : P.maxHeight = m + 1 :=
    (P.isGreatest_maxHeight hd).unique ⟨by simp [hP], by simp [hP, upperBounds]⟩
  have hw : P.weight = 1 := by
    have := P.natCast_weight
    rw [hmin, hmax] at this
    omega
  refine ⟨hmin, hw, ?_⟩
  simp [Parameters.hodgeVector_def, hw, List.range_succ, Parameters.hodgeNumber_def, hmin, hP]

theorem recordedHeights_zigzagLegendre : zigzagLegendre.recordedHeights = {0, 1} := by
  have hZ : zigzagLegendre.countingFunction (rep ((2⁻¹ : ℚ) : AddCircle (1 : ℚ))) = 2 := by
    rw [← one_div, rep_half, countingFunction_zigzagLegendre]
  rw [Parameters.recordedHeights_def, zigzagLegendre_α]
  simp [hZ]

example : zigzagLegendre.weight = 1 ∧ zigzagLegendre.hodgeVector = [1, 1] :=
  (weight_hodgeVector_of_recordedHeights (m := 0) (by simpa using
    recordedHeights_zigzagLegendre)).2

theorem countingFunction_zigzagHalfQuarter : zigzagHalfQuarter.countingFunction (1 / 2) = 1 := by
  simp only [Parameters.countingFunction_def, zigzagHalfQuarter_α, zigzagHalfQuarter_β,
    Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton, rep_half,
    rep_coe_of_mem (show (1 / 4 : ℚ) ∈ Ioc 0 1 by norm_num),
    rep_coe_of_mem (show (3 / 4 : ℚ) ∈ Ioc 0 1 by norm_num)]
  norm_num

theorem recordedHeights_zigzagHalfQuarter : zigzagHalfQuarter.recordedHeights = {-1, 0} := by
  have hZ : zigzagHalfQuarter.countingFunction (rep ((2⁻¹ : ℚ) : AddCircle (1 : ℚ))) = 1 := by
    rw [← one_div, rep_half, countingFunction_zigzagHalfQuarter]
  rw [Parameters.recordedHeights_def, zigzagHalfQuarter_α]
  simp [hZ]

example : zigzagHalfQuarter.minHeight = -1 ∧ zigzagHalfQuarter.weight = 1 ∧
    zigzagHalfQuarter.hodgeVector = [1, 1] :=
  weight_hodgeVector_of_recordedHeights (by simpa using recordedHeights_zigzagHalfQuarter)

-- For a pair of degree `0` the weight is `0` and the Hodge vector is `(0)`.
example (P : Parameters) (hP : P.degree = 0) : P.weight = 0 ∧ P.hodgeVector = [0] :=
  ⟨P.weight_of_degree_eq_zero hP, P.hodgeVector_of_degree_eq_zero hP⟩

end TauCeti.Hypergeometric.Examples
