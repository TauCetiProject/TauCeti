/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import TauCeti.Topology.MetricSpace.CoveringNumbers

/-!
# Packing and covering numbers from lower bounds on the measure of balls

Let `μ` be a measure on a pseudometric space and `A` a set. If every closed ball of radius `ε / 2`
centred at a point of `A` has measure at least `m`, then the number of points of a finite subset
of `A` any two of which are more than `ε` apart, times `m`, is at most `μ (cthickening (ε / 2) A)`.
Indeed the closed balls of radius `ε / 2` around such points are pairwise disjoint, and they lie
in the closed `ε / 2`-thickening of `A`. Consequently

`packingNumber ε A * m ≤ μ (cthickening (ε / 2) A)`,

and the same bound holds for the covering number. When moreover `m ≠ 0` and the thickening has
finite measure, these bounds say that the packing and covering numbers are at most
`μ (cthickening (ε / 2) A) / m`, and a maximal `ε`-separated subset of `A` realizes this bound by
a cover: it is a finite set of centres in `A` whose closed balls of radius `ε` cover `A` and whose
closed balls of radius `ε / 2` are pairwise disjoint.

The typical application is a lower density bound `μ (closedBall x ρ) ≥ c ρ ^ d` at the points
`x ∈ A`, valid on a window of radii `a ≤ ρ ≤ b`. Then for every `ε` with `2 a ≤ ε ≤ 2 b`,
`A` is covered by at most `2 ^ d μ (cthickening (ε / 2) A) / (c ε ^ d)` balls of radius `ε`
centred in `A`.

## Main results

* `Metric.IsSeparated.card_mul_le_measure_cthickening`: the cardinality of a finite
  `ε`-separated subset of `A`, times `m`, is at most `μ (cthickening (ε / 2) A)`.
* `TauCeti.packingNumber_mul_le_measure_cthickening`,
  `TauCeti.coveringNumber_mul_le_measure_cthickening`: the packing and covering numbers at scale
  `ε` times a lower bound for the measure of the balls of radius `ε / 2` centred in `A` are at
  most the measure of the closed `ε / 2`-thickening of `A`.
* `TauCeti.exists_finset_isCover_pairwiseDisjoint_closedBall`: if `m ≠ 0` and the thickening has
  finite measure, an `ε`-net of `A` by points of `A` with pairwise disjoint half-balls, whose
  cardinality times `m` is at most `μ (cthickening (ε / 2) A)`.
* `TauCeti.coveringNumber_le_of_mul_pow_le_measure_closedBall`: the covering number bound from a
  lower density bound `c ρ ^ d` on a window of radii.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {X : Type*} [PseudoMetricSpace X]

namespace Metric

variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {A : Set X} {ε : ℝ≥0}
  {m : ℝ≥0∞}

/-- If every closed ball of radius `ε / 2` centred at a point of an `ε`-separated finite subset `s`
of `A` has measure at least `m`, then the cardinality of `s` times `m` is at most
`μ (cthickening (ε / 2) A)`. -/
theorem IsSeparated.card_mul_le_measure_cthickening {s : Finset X} (hs : IsSeparated ε (s : Set X))
    (hsA : (s : Set X) ⊆ A) (hm : ∀ x ∈ s, m ≤ μ (closedBall x (ε / 2))) :
    s.card * m ≤ μ (cthickening (ε / 2) A) :=
  calc (s.card : ℝ≥0∞) * m
      = ∑ _x ∈ s, m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ s, μ (closedBall x (ε / 2)) := Finset.sum_le_sum hm
    _ = μ (⋃ x ∈ s, closedBall x (ε / 2)) :=
      (measure_biUnion_finset hs.pairwiseDisjoint_closedBall fun _ _ ↦
        measurableSet_closedBall).symm
    _ ≤ μ (cthickening (ε / 2) A) :=
      measure_mono <| iUnion₂_subset fun _ hx ↦ closedBall_subset_cthickening (hsA hx) _

end Metric

namespace TauCeti

variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {A : Set X} {ε : ℝ≥0}
  {m : ℝ≥0∞}

/-- **Packing bound from a lower bound on the measure of balls.** If every closed ball of radius
`ε / 2` centred at a point of `A` has measure at least `m`, then the packing number of `A` at scale
`ε` times `m` is at most the measure of the closed `ε / 2`-thickening of `A`. -/
theorem packingNumber_mul_le_measure_cthickening
    (hm : ∀ x ∈ A, m ≤ μ (closedBall x (ε / 2))) :
    (packingNumber ε A : ℝ≥0∞) * m ≤ μ (cthickening (ε / 2) A) := by
  rcases eq_or_ne m 0 with rfl | hm₀
  · simp
  rcases eq_or_ne (μ (cthickening (ε / 2) A)) ∞ with hμ | hμ
  · simp [hμ]
  have h := packingNumber_le_of_forall_finset_card_le (ENNReal.div_ne_top hμ hm₀)
    fun s hsA hs ↦ (ENNReal.le_div_iff_mul_le (.inl hm₀) (.inr hμ)).2 <|
      hs.card_mul_le_measure_cthickening hsA fun x hx ↦ hm x (hsA hx)
  exact (ENNReal.le_div_iff_mul_le (.inl hm₀) (.inr hμ)).1 h

/-- **Covering bound from a lower bound on the measure of balls.** If every closed ball of
radius `ε / 2` centred at a point of `A` has measure at least `m`, then the covering number of `A`
at scale `ε` times `m` is at most the measure of the closed `ε / 2`-thickening of `A`. -/
theorem coveringNumber_mul_le_measure_cthickening
    (hm : ∀ x ∈ A, m ≤ μ (closedBall x (ε / 2))) :
    (coveringNumber ε A : ℝ≥0∞) * m ≤ μ (cthickening (ε / 2) A) :=
  (mul_le_mul_left (ENat.toENNReal_le.2 (coveringNumber_le_packingNumber ε A)) m).trans
    (packingNumber_mul_le_measure_cthickening hm)

/-- **Maximal disjoint half-balls.** If every closed ball of radius `ε / 2` centred at a point of
`A` has measure at least `m ≠ 0`, and the closed `ε / 2`-thickening of `A` has finite measure,
then `A` has an `ε`-net `C ⊆ A` whose closed balls of radius `ε / 2` are pairwise disjoint and
whose cardinality is at most `μ (cthickening (ε / 2) A) / m`. -/
theorem exists_finset_isCover_pairwiseDisjoint_closedBall
    (hm : ∀ x ∈ A, m ≤ μ (closedBall x (ε / 2))) (hm₀ : m ≠ 0)
    (hμ : μ (cthickening (ε / 2) A) ≠ ∞) :
    ∃ C : Finset X, (C : Set X) ⊆ A ∧ IsCover ε A C ∧
      (C : Set X).PairwiseDisjoint (fun x ↦ closedBall x (ε / 2)) ∧
      C.card * m ≤ μ (cthickening (ε / 2) A) := by
  have hA : packingNumber ε A ≠ ⊤ := by
    intro h
    have := packingNumber_mul_le_measure_cthickening hm
    rw [h, ENat.toENNReal_top, ENNReal.top_mul hm₀, top_le_iff] at this
    exact hμ this
  have hC : (maximalSeparatedSet ε A).Finite := by
    rw [← Set.encard_ne_top_iff, encard_maximalSeparatedSet hA]
    exact hA
  have hsep : IsSeparated ε (hC.toFinset : Set X) := by
    simpa using isSeparated_maximalSeparatedSet
  have hsub : (hC.toFinset : Set X) ⊆ A := by simpa using maximalSeparatedSet_subset
  exact ⟨hC.toFinset, hsub, by simpa using isCover_maximalSeparatedSet hA,
    hsep.pairwiseDisjoint_closedBall,
    hsep.card_mul_le_measure_cthickening hsub fun x hx ↦ hm x (hsub hx)⟩

/-- **Covering bound from a lower density bound.** Suppose that `μ (closedBall x ρ) ≥ c ρ ^ d` for
every `x ∈ A` and every radius `a ≤ ρ ≤ b`, with `c > 0`. Then for every `ε > 0` with
`2 a ≤ ε ≤ 2 b`, the set `A` is covered by at most `2 ^ d μ (cthickening (ε / 2) A) / (c ε ^ d)`
closed balls of radius `ε` centred in `A`. -/
theorem coveringNumber_le_of_mul_pow_le_measure_closedBall {a b c : ℝ} {d : ℕ} (hc : 0 < c)
    (hA : ∀ x ∈ A, ∀ ρ, a ≤ ρ → ρ ≤ b → ENNReal.ofReal (c * ρ ^ d) ≤ μ (closedBall x ρ))
    (hε : ε ≠ 0) (haε : 2 * a ≤ ε) (hεb : ε ≤ 2 * b) :
    (coveringNumber ε A : ℝ≥0∞) ≤
      ENNReal.ofReal (2 ^ d / (c * ε ^ d)) * μ (cthickening (ε / 2) A) := by
  have hpos : 0 < c * ((ε : ℝ) / 2) ^ d := by positivity
  have h := coveringNumber_mul_le_measure_cthickening (μ := μ)
    fun x hx ↦ hA x hx (ε / 2) (by linarith) (by linarith)
  rw [← ENNReal.le_div_iff_mul_le (.inl (ENNReal.ofReal_pos.2 hpos).ne')
    (.inl ENNReal.ofReal_ne_top), ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hpos] at h
  convert h using 3
  rw [div_pow, mul_div_assoc', inv_div]

end TauCeti
