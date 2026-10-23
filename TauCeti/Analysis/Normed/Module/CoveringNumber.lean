/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Algebra.Order.Floor.Extended

/-!
# Volumetric bounds on covering and packing numbers

In a real normed space `E` of finite dimension `n`, a set of points of a closed ball of radius `r`
any two of which are more than `ε > 0` apart has at most `(1 + 2 r / ε) ^ n` elements. Indeed, the
open balls of radius `ε / 2` around these points are pairwise disjoint and lie in the ball of
radius `r + ε / 2` around the centre, and a Haar measure scales the volume of a ball of radius
`ρ` by `ρ ^ n`. Hence the packing number, and with it the covering number, of a subset of a ball
is at most `(1 + 2 r / ε) ^ n`.

In particular the unit sphere of `E` has an `η`-net of at most `(1 + 2 / η) ^ n` points, for every
`η > 0`. Nets of this size on the Euclidean sphere `Sⁿ⁻¹` drive the passage from concentration of
measure at single points to uniform estimates on whole subspaces, as in the proof of Dvoretzky's
theorem on almost Euclidean sections of finite-dimensional normed spaces.

## Main results

* `TauCeti.card_le_of_isSeparated_of_subset_closedBall`: an `ε`-separated finite subset of a closed
  ball of radius `r` has at most `(1 + 2 r / ε) ^ n` elements.
* `TauCeti.packingNumber_le_of_subset_closedBall`,
  `TauCeti.coveringNumber_le_of_subset_closedBall`: the corresponding bounds on the packing and
  covering numbers of a subset of a closed ball.
* `TauCeti.exists_finset_isCover_of_subset_closedBall`: a subset of a closed ball of radius `r`
  has an `ε`-net consisting of at most `(1 + 2 r / ε) ^ n` of its points.
* `TauCeti.exists_finset_isCover_sphere`: the unit sphere has an `η`-net consisting of at most
  `(1 + 2 / η) ^ n` of its points.

## References

* R. Vershynin, *High-Dimensional Probability*, §4.2, Proposition 4.2.12 and Corollary 4.2.13.
* The volume argument follows Mathlib's `Besicovitch.card_le_of_separated`, which treats
  `1`-separated subsets of the ball of radius `2`.
-/

public section

open Metric MeasureTheory Module Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : Set E} {x : E} {r ε : ℝ≥0}

/-- **Volumetric packing bound.** In a finite-dimensional real normed space, a finite subset of a
closed ball of radius `r` whose points are pairwise more than `ε > 0` apart has at most
`(1 + 2 r / ε) ^ dim E` elements. -/
theorem card_le_of_isSeparated_of_subset_closedBall {s : Finset E} (hε : ε ≠ 0)
    (hs : IsSeparated ε (s : Set E)) (hsx : (s : Set E) ⊆ closedBall x r) :
    (s.card : ℝ) ≤ (1 + 2 * r / ε) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  set δ : ℝ := ε / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hρ : 0 < r + δ := by positivity
  -- The balls of radius `δ = ε / 2` around the points of `s` are pairwise disjoint ...
  have hdisj : (s : Set E).PairwiseDisjoint fun y ↦ ball y δ := by
    intro y hy z hz hyz
    refine ball_disjoint_ball ?_
    have hyz' : (ε : ℝ≥0∞) < edist y z := hs hy hz hyz
    rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at hyz'
    linarith
  -- ... and lie in the ball of radius `r + δ` around `x`.
  have hsub : (⋃ y ∈ s, ball y δ) ⊆ ball x (r + δ) := by
    refine iUnion₂_subset fun y hy ↦ ball_subset_ball' ?_
    linarith [mem_closedBall.1 (hsx hy)]
  have key : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((r + δ) ^ finrank ℝ E) * μ (ball 0 1) :=
    calc (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1)
        = μ (⋃ y ∈ s, ball y δ) := by
          rw [measure_biUnion_finset hdisj fun _ _ ↦ measurableSet_ball]
          simp [μ.addHaar_ball_of_pos _ hδ, mul_assoc]
      _ ≤ μ (ball x (r + δ)) := measure_mono hsub
      _ = ENNReal.ofReal ((r + δ) ^ finrank ℝ E) * μ (ball 0 1) := μ.addHaar_ball_of_pos _ hρ
  have hcard : (s.card : ℝ) * δ ^ finrank ℝ E ≤ (r + δ) ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
        measure_ball_lt_top.ne).1 key)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_natCast] at h
  have hratio : (1 + 2 * r / ε : ℝ) = (r + δ) / δ := by
    rw [hδ_def]
    field_simp
    ring
  rw [hratio, div_pow, le_div_iff₀ (by positivity)]
  exact hcard

/-- The packing number at scale `ε > 0` of a subset of a closed ball of radius `r` in a
finite-dimensional real normed space is at most `(1 + 2 r / ε) ^ dim E`. -/
theorem packingNumber_le_of_subset_closedBall (hε : ε ≠ 0) (hA : A ⊆ closedBall x r) :
    (packingNumber ε A : ℝ≥0∞) ≤ (1 + 2 * r / ε) ^ finrank ℝ E := by
  -- The bound, as an extended real number, on the size of a finite separated subset of `A`.
  have hB : ENNReal.ofReal ((1 + 2 * r / ε) ^ finrank ℝ E) =
      (1 + 2 * (r : ℝ≥0∞) / ε) ^ finrank ℝ E := by
    have h : (1 + 2 * r / ε : ℝ) = ((1 + 2 * r / ε : ℝ≥0) : ℝ) := by simp
    rw [ENNReal.ofReal_pow (by positivity), h, ENNReal.ofReal_coe_nnreal]
    simp [ENNReal.coe_div hε]
  have hfin : ∀ s : Finset E, (s : Set E) ⊆ A → IsSeparated ε (s : Set E) →
      (s.card : ℝ≥0∞) ≤ (1 + 2 * (r : ℝ≥0∞) / ε) ^ finrank ℝ E := fun s hsA hs ↦ by
    rw [← hB, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal
      (card_le_of_isSeparated_of_subset_closedBall hε hs (hsA.trans hA))
  rw [packingNumber]
  simp only [ENat.toENNReal_iSup]
  refine iSup₂_le fun C hCA ↦ iSup_le fun hC ↦ ?_
  rcases C.finite_or_infinite with hCf | hCi
  · rw [hCf.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    exact hfin hCf.toFinset (by simpa using hCA) (by simpa using hC)
  · -- An infinite separated subset would contain finite separated subsets of every size.
    exfalso
    have hB_ne : (1 + 2 * (r : ℝ≥0∞) / ε) ^ finrank ℝ E ≠ ∞ := hB ▸ ENNReal.ofReal_ne_top
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hB_ne
    obtain ⟨s, hsC, rfl⟩ := hCi.exists_subset_card_eq n
    exact (hfin s (hsC.trans hCA) (hC.subset hsC)).not_gt hn

/-- The covering number at scale `ε > 0` of a subset of a closed ball of radius `r` in a
finite-dimensional real normed space is at most `(1 + 2 r / ε) ^ dim E`. -/
theorem coveringNumber_le_of_subset_closedBall (hε : ε ≠ 0) (hA : A ⊆ closedBall x r) :
    (coveringNumber ε A : ℝ≥0∞) ≤ (1 + 2 * r / ε) ^ finrank ℝ E :=
  (ENat.toENNReal_le.2 (coveringNumber_le_packingNumber ε A)).trans
    (packingNumber_le_of_subset_closedBall hε hA)

/-- A subset `A` of a closed ball of radius `r` in a finite-dimensional real normed space has an
`ε`-net, for `ε > 0`, consisting of at most `(1 + 2 r / ε) ^ dim E` points of `A`. -/
theorem exists_finset_isCover_of_subset_closedBall (hε : ε ≠ 0) (hA : A ⊆ closedBall x r) :
    ∃ N : Finset E, (N : Set E) ⊆ A ∧ IsCover ε A N ∧
      (N.card : ℝ) ≤ (1 + 2 * r / ε) ^ finrank ℝ E := by
  have hA_top : packingNumber ε A ≠ ⊤ :=
    ENat.toENNReal_ne_top.1 <| ne_top_of_le_ne_top
      (ENNReal.pow_ne_top (by simp [ENNReal.div_eq_top, ENNReal.mul_eq_top, hε]))
      (packingNumber_le_of_subset_closedBall hε hA)
  have hNf : (maximalSeparatedSet ε A).Finite := by
    rw [← Set.encard_ne_top_iff, encard_maximalSeparatedSet hA_top]
    exact hA_top
  refine ⟨hNf.toFinset, by simpa using maximalSeparatedSet_subset, by
    simpa using isCover_maximalSeparatedSet hA_top, ?_⟩
  exact card_le_of_isSeparated_of_subset_closedBall hε
    (by simpa using isSeparated_maximalSeparatedSet)
    (by simpa using maximalSeparatedSet_subset.trans hA)

/-- The unit sphere of a finite-dimensional real normed space `E` has an `η`-net, for `η > 0`,
consisting of at most `(1 + 2 / η) ^ dim E` points of the sphere. -/
theorem exists_finset_isCover_sphere {η : ℝ≥0} (hη : η ≠ 0) :
    ∃ N : Finset E, (N : Set E) ⊆ sphere 0 1 ∧ IsCover η (sphere (0 : E) 1) N ∧
      (N.card : ℝ) ≤ (1 + 2 / η) ^ finrank ℝ E := by
  simpa using exists_finset_isCover_of_subset_closedBall (r := 1) hη
    (sphere_subset_closedBall (x := (0 : E)))

end TauCeti
