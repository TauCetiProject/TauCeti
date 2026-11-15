/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Covering.PackingNumber

/-!
# Volumetric bounds on covering and packing numbers

In a real normed space `E` of finite dimension `n`, a set of points of a closed ball of radius `r`
any two of which are more than `ε > 0` apart has at most `(1 + 2 r / ε) ^ n` elements. Indeed,
the closed balls of radius `ε / 2` around these points are pairwise disjoint and lie in the closed
ball of radius `r + ε / 2` around the centre
(`Metric.IsSeparated.card_mul_le_measure_cthickening`), and a Haar measure scales the volume of a
ball of radius `ρ` by `ρ ^ n`. Hence the packing number, and with it the covering number, of a
subset of a ball is at most `(1 + 2 r / ε) ^ n`.

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
* `TauCeti.pow_finrank_le_card_mul_pow_of_isCover_closedBall` and
  `TauCeti.div_pow_finrank_le_externalCoveringNumber_closedBall`: volumetric lower bounds
  `r ^ n ≤ N.card * ε ^ n` and `(r / ε) ^ n ≤ externalCoveringNumber ε (closedBall x r)` on covers
  of a closed ball.

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
  -- The closed balls of radius `δ = ε / 2` around the points of `s` are disjoint and lie in the
  -- closed ball of radius `r + δ` around `x`.
  have hsub : cthickening δ (s : Set E) ⊆ closedBall x (r + δ) := by
    rw [add_comm]
    exact (cthickening_subset_of_subset δ hsx).trans (cthickening_closedBall hδ.le r.2 x).le
  have key : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((r + δ) ^ finrank ℝ E) * μ (ball 0 1) :=
    calc (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1)
        ≤ μ (cthickening δ (s : Set E)) := by
          rw [mul_assoc]
          exact hs.card_mul_le_measure_cthickening subset_rfl fun _ _ ↦
            (μ.addHaar_closedBall _ hδ.le).ge
      _ ≤ μ (closedBall x (r + δ)) := measure_mono hsub
      _ = ENNReal.ofReal ((r + δ) ^ finrank ℝ E) * μ (ball 0 1) :=
          μ.addHaar_closedBall _ hρ.le
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
  refine packingNumber_le_of_forall_finset_card_le (hB ▸ ENNReal.ofReal_ne_top)
    fun s hsA hs ↦ ?_
  rw [← hB, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (card_le_of_isSeparated_of_subset_closedBall hε hs (hsA.trans hA))

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

/-- **Volumetric covering lower bound.** If a closed ball of radius `r` in a finite-dimensional
real normed space is covered by a finite `ε`-net `N`, then `r ^ dim E ≤ N.card * ε ^ dim E`. -/
theorem pow_finrank_le_card_mul_pow_of_isCover_closedBall {N : Finset E}
    (hcov : IsCover ε (closedBall x r) N) :
    (r : ℝ) ^ finrank ℝ E ≤ N.card * (ε : ℝ) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have key : ENNReal.ofReal ((r : ℝ) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((N.card : ℝ) * (ε : ℝ) ^ finrank ℝ E) * μ (ball 0 1) :=
    calc ENNReal.ofReal ((r : ℝ) ^ finrank ℝ E) * μ (ball 0 1)
        = μ (closedBall x r) := (μ.addHaar_closedBall x r.2).symm
      _ ≤ μ (⋃ y ∈ (N : Set E), closedBall y ε) := measure_mono hcov.subset_iUnion_closedBall
      _ ≤ ∑ y ∈ N, μ (closedBall y ε) := measure_biUnion_finset_le N fun y ↦ closedBall y ε
      _ = ∑ _y ∈ N, ENNReal.ofReal ((ε : ℝ) ^ finrank ℝ E) * μ (ball 0 1) :=
          Finset.sum_congr rfl fun y _ ↦ μ.addHaar_closedBall y ε.2
      _ = ENNReal.ofReal ((N.card : ℝ) * (ε : ℝ) ^ finrank ℝ E) * μ (ball 0 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have h := ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 key)
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

/-- **Volumetric external covering lower bound.** At scale `ε > 0`, the external covering number
of a closed ball of radius `r` in a finite-dimensional real normed space is at least
`(r / ε) ^ dim E`. -/
theorem div_pow_finrank_le_externalCoveringNumber_closedBall (x : E) (r : ℝ≥0) (hε : ε ≠ 0) :
    ((r : ℝ≥0∞) / ε) ^ finrank ℝ E ≤ externalCoveringNumber ε (closedBall x r) := by
  rcases eq_top_or_lt_top (externalCoveringNumber ε (closedBall x r)) with htop | hlt
  · simp [htop]
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  rw [← hk]
  obtain ⟨N, hNk, hcov⟩ := externalCoveringNumber_le_natCast_iff.mp hk.ge
  have hcard := pow_finrank_le_card_mul_pow_of_isCover_closedBall hcov
  have hdiv : ((r / ε : ℝ) ^ finrank ℝ E) ≤ k := by
    refine ((div_pow (r : ℝ) (ε : ℝ) (finrank ℝ E)).trans_le ?_).trans (Nat.cast_le.mpr hNk)
    rwa [div_le_iff₀ (by positivity)]
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine (le_of_eq ?_).trans (ENNReal.ofReal_le_ofReal hdiv)
  rw [ENNReal.ofReal_pow (by positivity), ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_div hε]

end TauCeti
