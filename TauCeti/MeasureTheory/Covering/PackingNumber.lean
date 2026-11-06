/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Algebra.Order.Floor.Extended

/-!
# Packing numbers of sets on which a measure has a lower density bound

Let `μ` be a measure on a pseudo-emetric space and let `A` be a set such that every open ball of
radius `ε / 2` centred at a point of `A` has measure at least `a`, and lies inside a fixed set `U`.
The balls of radius `ε / 2` around the points of an `ε`-separated subset of `A` are pairwise
disjoint, so such a subset has at most `μ U / a` points. Hence the packing number of `A` at scale
`ε` (`Metric.packingNumber`) is at most `μ U / a`.

When `a` is positive and `μ U` is finite, `A` therefore has a finite maximal `ε`-separated subset
`C`. Its points are centres of pairwise disjoint balls of radius `ε / 2`, the closed balls of
radius `ε` around them cover `A`, and `#C · a ≤ μ U`.

If the lower bound has the power form `μ (ball x (ε / 2)) ≥ c (ε / 2) ^ d` for some `c > 0`, the
bound becomes `N(ε) ≤ 2 ^ d μ U / (c ε ^ d)`. The constant `2 ^ d μ U / c` depends only on the
density constant `c`, the exponent `d` and the mass `μ U`, so a family of measures and sets with
uniform such bounds has uniformly bounded packing numbers `N(ε) ≤ C ε ^ (-d)`. This is the
counting step in Taubes's analysis of the zero set of the Seiberg–Witten section `α` at large
`r`: the local defect energy is at least `c σ²` on a ball of radius `σ` centred at a zero, and
its total mass is bounded independently of `r`, so the zero set is covered by `O(σ⁻²)` balls of
radius `σ` centred at zeros, with disjoint half-balls.

For a Haar measure on a finite-dimensional real normed space, the same volume argument gives the
bounds of `TauCeti.Analysis.Normed.Module.CoveringNumber` on subsets of a ball.

## Main results

* `Metric.IsSeparated.pairwiseDisjoint_eball`: the balls of radius `ε / 2` around the points of an
  `ε`-separated set are pairwise disjoint.
* `Metric.IsSeparated.encard_mul_le_measure`: an `ε`-separated set `C` whose half-balls have
  measure at least `a` and lie in `U` satisfies `#C · a ≤ μ U`.
* `Metric.packingNumber_mul_le_measure`: the packing number bound `N(ε) · a ≤ μ U`.
* `Metric.exists_finite_isSeparated_isCover_encard_mul_le_measure`: a finite `ε`-separated subset
  of `A` whose closed `ε`-balls cover `A`, with at most `μ U / a` points.
* `Metric.packingNumber_le_of_mul_rpow_le_measure`: the power form
  `N(ε) ≤ 2 ^ d μ U / (c ε ^ d)`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* R. Vershynin, *High-Dimensional Probability*, Cambridge University Press (2018), Section 4.2.
-/

public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-- The open balls of radius `ε / 2` around the points of an `ε`-separated set are pairwise
disjoint. -/
theorem IsSeparated.pairwiseDisjoint_eball {ε : ℝ≥0∞} {C : Set X} (hC : IsSeparated ε C) :
    C.PairwiseDisjoint fun x ↦ eball x (ε / 2) := fun _ hx _ hy hxy ↦
  eball_disjoint <| (ENNReal.add_halves ε).trans_le (hC hx hy hxy).le

variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {A U : Set X} {a : ℝ≥0∞}

/-- If the balls of radius `ε / 2` around the points of an `ε`-separated set `C` have measure at
least `a` and lie in `U`, then `C` has at most `μ U / a` points. -/
theorem IsSeparated.encard_mul_le_measure {ε : ℝ≥0∞} {C : Set X} (hC : IsSeparated ε C)
    (ha : ∀ x ∈ C, a ≤ μ (eball x (ε / 2))) (hU : ∀ x ∈ C, eball x (ε / 2) ⊆ U) :
    (C.encard : ℝ≥0∞) * a ≤ μ U :=
  calc (C.encard : ℝ≥0∞) * a = ∑' _ : C, a := by
        rw [ENNReal.tsum_const, ENat.card_coe_set_eq]
    _ ≤ ∑' x : C, μ (eball (x : X) (ε / 2)) := tsum_le_tsum fun x ↦ ha x x.2
    _ ≤ μ (⋃ x : C, eball (x : X) (ε / 2)) :=
        tsum_meas_le_meas_iUnion_of_disjoint μ (fun _ ↦ isOpen_eball.measurableSet)
          fun x y hxy ↦ hC.pairwiseDisjoint_eball x.2 y.2 (Subtype.coe_ne_coe.2 hxy)
    _ ≤ μ U := measure_mono <| iUnion_subset fun x ↦ hU x x.2

/-- **Packing number bound from a lower density bound.** If every ball of radius `ε / 2` centred
at a point of `A` has measure at least `a` and lies in `U`, then the packing number of `A` at
scale `ε` is at most `μ U / a`. -/
theorem packingNumber_mul_le_measure {ε : ℝ≥0} (ha : ∀ x ∈ A, a ≤ μ (eball x (ε / 2)))
    (hU : ∀ x ∈ A, eball x (ε / 2) ⊆ U) : (packingNumber ε A : ℝ≥0∞) * a ≤ μ U := by
  simp only [packingNumber, ENat.toENNReal_iSup, ENNReal.iSup_mul, iSup_le_iff]
  exact fun C hCA hC ↦
    hC.encard_mul_le_measure (fun x hx ↦ ha x (hCA hx)) fun x hx ↦ hU x (hCA hx)

/-- Under a positive lower bound on the measure of the balls of radius `ε / 2` centred at the
points of `A`, all lying in a set `U` of finite measure, the packing number of `A` at scale `ε`
is finite. -/
theorem packingNumber_ne_top_of_le_measure {ε : ℝ≥0} (ha₀ : a ≠ 0) (hμU : μ U ≠ ∞)
    (ha : ∀ x ∈ A, a ≤ μ (eball x (ε / 2))) (hU : ∀ x ∈ A, eball x (ε / 2) ⊆ U) :
    packingNumber ε A ≠ ⊤ := by
  intro h
  have := packingNumber_mul_le_measure ha hU
  rw [h, ENat.toENNReal_top, ENNReal.top_mul ha₀, top_le_iff] at this
  exact hμU this

/-- **Covering by disjoint half-balls.** If every ball of radius `ε / 2` centred at a point of `A`
has measure at least `a ≠ 0` and lies in a set `U` of finite measure, then `A` has a finite
`ε`-separated subset `C` (so the balls of radius `ε / 2` around its points are pairwise disjoint,
by `Metric.IsSeparated.pairwiseDisjoint_eball`) whose closed balls of radius `ε` cover `A`, and
`C` has at most `μ U / a` points. -/
theorem exists_finite_isSeparated_isCover_encard_mul_le_measure {ε : ℝ≥0} (ha₀ : a ≠ 0)
    (hμU : μ U ≠ ∞) (ha : ∀ x ∈ A, a ≤ μ (eball x (ε / 2)))
    (hU : ∀ x ∈ A, eball x (ε / 2) ⊆ U) :
    ∃ C ⊆ A, C.Finite ∧ IsSeparated ε C ∧ IsCover ε A C ∧ (C.encard : ℝ≥0∞) * a ≤ μ U := by
  have h := packingNumber_ne_top_of_le_measure ha₀ hμU ha hU
  refine ⟨maximalSeparatedSet ε A, maximalSeparatedSet_subset, ?_,
    isSeparated_maximalSeparatedSet, isCover_maximalSeparatedSet h, ?_⟩
  · rw [← Set.encard_ne_top_iff, encard_maximalSeparatedSet h]
    exact h
  · rw [encard_maximalSeparatedSet h]
    exact packingNumber_mul_le_measure ha hU

/-- **Power-law packing bound.** If every ball of radius `ε / 2` centred at a point of `A` has
measure at least `c (ε / 2) ^ d`, with `c ≠ 0` and `ε ≠ 0`, and lies in `U`, then the packing
number of `A` at scale `ε` is at most `2 ^ d μ U / (c ε ^ d)`. -/
theorem packingNumber_le_of_mul_rpow_le_measure {ε c : ℝ≥0} {d : ℝ} (hε : ε ≠ 0) (hc : c ≠ 0)
    (ha : ∀ x ∈ A, c * (ε / 2 : ℝ≥0∞) ^ d ≤ μ (eball x (ε / 2)))
    (hU : ∀ x ∈ A, eball x (ε / 2) ⊆ U) :
    (packingNumber ε A : ℝ≥0∞) ≤ 2 ^ d * μ U / (c * ε ^ d) := by
  have hε₀ : (ε : ℝ≥0∞) ≠ 0 := by simpa using hε
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl (mul_ne_zero (by simpa using hc) (by simp [ENNReal.rpow_eq_zero_iff, hε₀])))
    (Or.inl (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg' (pos_iff_ne_zero.2 hε₀) ENNReal.coe_ne_top)))]
  calc (packingNumber ε A : ℝ≥0∞) * (c * ε ^ d)
      = (packingNumber ε A : ℝ≥0∞) * (c * (ε / 2 : ℝ≥0∞) ^ d) * 2 ^ d := by
        rw [mul_assoc, mul_assoc, ← ENNReal.mul_rpow_of_ne_top
            (ENNReal.div_ne_top ENNReal.coe_ne_top two_ne_zero) ENNReal.ofNat_ne_top,
          ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
    _ ≤ μ U * 2 ^ d := mul_le_mul_left (packingNumber_mul_le_measure ha hU) _
    _ = 2 ^ d * μ U := mul_comm _ _

end Metric
