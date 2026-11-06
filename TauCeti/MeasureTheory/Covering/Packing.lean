/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Basic.Real.ENatENNReal

/-!
# Packing bounds from lower bounds on the mass of balls

Let `μ` be a measure on a pseudo-metric space and `A` a set at whose points every open ball of
radius `ε / 2` has `μ`-mass at least `m`. If the points of `C ⊆ A` are pairwise more than `ε`
apart, the balls of radius `ε / 2` around them are pairwise disjoint and lie in the
`ε / 2`-thickening of `A`, so `C` has at most `μ (thickening (ε / 2) A) / m` points. Hence the
packing number, and with it the covering number, of `A` at scale `ε` is bounded by the mass of
that thickening divided by `m`. When this mass is finite and `m ≠ 0`, a maximal `ε`-separated
subset of `A` is a finite set of centres in `A` whose closed `ε`-balls cover `A`, whose open
`ε / 2`-balls are disjoint, and whose cardinality obeys the same bound.

If the lower bound is a power law, `μ (ball x ρ) ≥ c ρ ^ d` at `ρ = ε / 2`, the number of centres
is at most `2 ^ d M / (c ε ^ d)` when `M` bounds the mass of the thickening. For `d = 2` this is the
covering bound `N(σ) ≤ C σ⁻²` used to count the balls of radius `σ` centred on the zero set of the
spinor component `α` of a Seiberg–Witten solution with large perturbation parameter `r` on a
symplectic four-manifold, with `μ` the defect measure `(r / 4) |1 - |ψ|²| dvol`. There the lower
bound comes from the monotonicity inequality in the quadratic form `m ρ² ≤ μ (ball x ρ) + a ρ⁴`
on a window of radii `c₀ h ≤ ρ ≤ ρ₁`, with `h = r ^ (-1/2)`
(`TauCeti.mul_sq_le_add_of_le_mul_deriv_add`). The window version below absorbs the quartic
term at small radii and records the quantifier: the bound at scale `σ` holds as soon as
`2 c₀ h ≤ σ`, that is, for all `r` beyond a threshold depending on `σ`.

## Main results

* `Metric.IsSeparated.pairwiseDisjoint_ball`: the open `ε / 2`-balls around the points of an
  `ε`-separated set are pairwise disjoint.
* `Metric.IsSeparated.encard_mul_le_measure_thickening`: an `ε`-separated set `C` all of whose
  `ε / 2`-balls have mass at least `m` satisfies `card C * m ≤ μ (thickening (ε / 2) C)`.
* `TauCeti.packingNumber_mul_le_measure_thickening`,
  `TauCeti.coveringNumber_mul_le_measure_thickening`: the corresponding bounds on the packing and
  covering numbers.
* `TauCeti.exists_finset_isSeparated_isCover_card_mul_le`: a finite `ε`-separated `ε`-net of `A`
  inside `A` with at most `μ (thickening (ε / 2) A) / m` points.
* `TauCeti.exists_finset_isSeparated_isCover_card_le_of_mul_pow_le`: the same under a power-law
  lower bound, with at most `2 ^ d M / (c ε ^ d)` points.
* `TauCeti.exists_finset_isSeparated_isCover_card_le_of_mul_sq_le_measure_ball_add`: the quadratic
  window version, with at most `8 M / (m σ ^ 2)` points.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. **9** (1996), 845–918.
* R. Vershynin, *High-Dimensional Probability*, §4.2 (packing and covering numbers).
-/

public section

open Metric MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [PseudoMetricSpace X] {ε : ℝ≥0} {A C : Set X}

namespace Metric.IsSeparated

/-- The open balls of radius `ε / 2` around the points of an `ε`-separated set are pairwise
disjoint. -/
theorem pairwiseDisjoint_ball (hC : IsSeparated ε C) :
    C.PairwiseDisjoint fun x ↦ ball x (ε / 2 : ℝ) := by
  intro x hx y hy hxy
  refine ball_disjoint_ball ?_
  have h : (ε : ℝ≥0∞) < edist x y := hC hx hy hxy
  rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at h
  linarith

variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {m : ℝ≥0∞}

/-- **Mass packing bound.** If the points of `C` are pairwise more than `ε` apart and every open
ball of radius `ε / 2` centred in `C` has `μ`-mass at least `m`, then
`card C * m ≤ μ (thickening (ε / 2) C)`. In particular `C` is finite when `m ≠ 0` and the
thickening has finite mass. -/
theorem encard_mul_le_measure_thickening (hC : IsSeparated ε C)
    (hm : ∀ x ∈ C, m ≤ μ (ball x (ε / 2 : ℝ))) :
    (C.encard : ℝ≥0∞) * m ≤ μ (thickening (ε / 2 : ℝ) C) := by
  -- The bound for every finite subset of `C`, by additivity over the disjoint balls.
  have key (s : Finset X) (hs : (s : Set X) ⊆ C) :
      (s.card : ℝ≥0∞) * m ≤ μ (thickening (ε / 2 : ℝ) C) :=
    calc (s.card : ℝ≥0∞) * m = ∑ _ ∈ s, m := by simp
      _ ≤ ∑ x ∈ s, μ (ball x (ε / 2 : ℝ)) := Finset.sum_le_sum fun x hx ↦ hm x (hs hx)
      _ = μ (⋃ x ∈ s, ball x (ε / 2 : ℝ)) :=
        (measure_biUnion_finset (hC.subset hs).pairwiseDisjoint_ball
          fun _ _ ↦ measurableSet_ball).symm
      _ ≤ μ (thickening (ε / 2 : ℝ) C) := by
        rw [thickening_eq_biUnion_ball]
        exact measure_mono (biUnion_subset_biUnion_left hs)
  rcases C.finite_or_infinite with hCf | hCi
  · rw [hCf.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    exact key hCf.toFinset (by simp)
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  -- An infinite `C` contains finite subsets of every size, which force infinite mass.
  rw [hCi.encard_eq, ENat.toENNReal_top, ENNReal.top_mul hm0, top_le_iff]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hm0 (ENNReal.coe_ne_top (r := r))
  obtain ⟨s, hsC, rfl⟩ := hCi.exists_subset_card_eq n
  exact hn.le.trans (key s hsC)

end Metric.IsSeparated

namespace TauCeti

variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {m : ℝ≥0∞}

/-- If every open ball of radius `ε / 2` centred in `A` has `μ`-mass at least `m`, the packing
number of `A` at scale `ε` satisfies `packingNumber ε A * m ≤ μ (thickening (ε / 2) A)`. -/
theorem packingNumber_mul_le_measure_thickening (hm : ∀ x ∈ A, m ≤ μ (ball x (ε / 2 : ℝ))) :
    (packingNumber ε A : ℝ≥0∞) * m ≤ μ (thickening (ε / 2 : ℝ) A) := by
  simp only [packingNumber, ENat.toENNReal_iSup, ENNReal.iSup_mul]
  refine iSup₂_le fun C hCA ↦ iSup_le fun hC ↦ ?_
  exact (hC.encard_mul_le_measure_thickening fun x hx ↦ hm x (hCA hx)).trans
    (measure_mono (thickening_subset_of_subset _ hCA))

/-- If every open ball of radius `ε / 2` centred in `A` has `μ`-mass at least `m`, the covering
number of `A` at scale `ε` satisfies `coveringNumber ε A * m ≤ μ (thickening (ε / 2) A)`. -/
theorem coveringNumber_mul_le_measure_thickening (hm : ∀ x ∈ A, m ≤ μ (ball x (ε / 2 : ℝ))) :
    (coveringNumber ε A : ℝ≥0∞) * m ≤ μ (thickening (ε / 2 : ℝ) A) :=
  (mul_le_mul_left (ENat.toENNReal_le.2 (coveringNumber_le_packingNumber ε A)) m).trans
    (packingNumber_mul_le_measure_thickening hm)

/-- **Maximal-disjoint-ball covering.** If every open ball of radius `ε / 2` centred in `A` has
`μ`-mass at least `m ≠ 0` and the `ε / 2`-thickening of `A` has finite mass, then `A` has a
finite `ε`-separated subset `N` (so the open `ε / 2`-balls around `N` are disjoint) whose closed
`ε`-balls cover `A`, with `card N * m ≤ μ (thickening (ε / 2) A)`. -/
theorem exists_finset_isSeparated_isCover_card_mul_le (hm0 : m ≠ 0)
    (hA : μ (thickening (ε / 2 : ℝ) A) ≠ ∞) (hm : ∀ x ∈ A, m ≤ μ (ball x (ε / 2 : ℝ))) :
    ∃ N : Finset X, (N : Set X) ⊆ A ∧ IsSeparated ε (N : Set X) ∧ IsCover ε A (N : Set X) ∧
      (N.card : ℝ≥0∞) * m ≤ μ (thickening (ε / 2 : ℝ) A) := by
  have htop : packingNumber ε A ≠ ⊤ := by
    intro h
    have hle := packingNumber_mul_le_measure_thickening hm
    rw [h, ENat.toENNReal_top, ENNReal.top_mul hm0, top_le_iff] at hle
    exact hA hle
  have hNf : (maximalSeparatedSet ε A).Finite := by
    rw [← encard_ne_top_iff, encard_maximalSeparatedSet htop]
    exact htop
  have hcard := isSeparated_maximalSeparatedSet.encard_mul_le_measure_thickening
    fun x hx ↦ hm x (maximalSeparatedSet_subset hx)
  rw [hNf.encard_eq_coe_toFinset_card, ENat.toENNReal_coe] at hcard
  exact ⟨hNf.toFinset, by simpa using maximalSeparatedSet_subset,
    by simpa using isSeparated_maximalSeparatedSet,
    by simpa using isCover_maximalSeparatedSet htop,
    hcard.trans (measure_mono (thickening_subset_of_subset _ maximalSeparatedSet_subset))⟩

/-- **Packing under a power-law lower bound.** If every open ball of radius `ε / 2 > 0` centred
in `A` has `μ`-mass at least `c (ε / 2) ^ d` with `c > 0`, and the `ε / 2`-thickening of `A` has
mass at most `M`, then `A` has a finite `ε`-separated subset whose closed `ε`-balls cover `A` and
which has at most `2 ^ d M / (c ε ^ d)` points. -/
theorem exists_finset_isSeparated_isCover_card_le_of_mul_pow_le {c M : ℝ} {d : ℕ} (hc : 0 < c)
    (hε : ε ≠ 0) (hM : 0 ≤ M) (hAM : μ (thickening (ε / 2 : ℝ) A) ≤ ENNReal.ofReal M)
    (hm : ∀ x ∈ A, ENNReal.ofReal (c * (ε / 2 : ℝ) ^ d) ≤ μ (ball x (ε / 2 : ℝ))) :
    ∃ N : Finset X, (N : Set X) ⊆ A ∧ IsSeparated ε (N : Set X) ∧ IsCover ε A (N : Set X) ∧
      (N.card : ℝ) ≤ 2 ^ d * M / (c * ε ^ d) := by
  have hε' : (0 : ℝ) < ε := by positivity
  have hpos : 0 < c * (ε / 2 : ℝ) ^ d := by positivity
  obtain ⟨N, hNA, hN, hNcov, hcard⟩ := exists_finset_isSeparated_isCover_card_mul_le
    (ENNReal.ofReal_pos.2 hpos).ne' (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAM) hm
  refine ⟨N, hNA, hN, hNcov, ?_⟩
  have h : (N.card : ℝ) * (c * (ε / 2 : ℝ) ^ d) ≤ M := by
    rw [← ENNReal.ofReal_le_ofReal_iff hM, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
    exact hcard.trans hAM
  rw [le_div_iff₀ (by positivity)]
  calc (N.card : ℝ) * (c * ε ^ d) = 2 ^ d * ((N.card : ℝ) * (c * (ε / 2 : ℝ) ^ d)) := by
        rw [div_pow]
        field_simp
    _ ≤ 2 ^ d * M := by gcongr

/-- **Packing on a window of scales.** Suppose that at every point `x` of `A` the masses of
balls satisfy the quadratic lower bound `m ρ ^ 2 ≤ μ (ball x ρ) + a ρ ^ 4` for all radii
`c₀ h ≤ ρ ≤ ρ₁`, with `m > 0`. Then for every scale `σ > 0` with
`2 c₀ h ≤ σ ≤ 2 ρ₁` and `a σ ^ 2 ≤ 2 m`, whose `σ / 2`-thickening of `A` has mass at most `M`,
the set `A` has a finite `σ`-separated subset whose closed `σ`-balls cover `A` and which has at
most `8 M / (m σ ^ 2)` points.

With `h = r ^ (-1/2)`, the condition `2 c₀ h ≤ σ` says that `r` is at least `(2 c₀ / σ) ^ 2`. -/
theorem exists_finset_isSeparated_isCover_card_le_of_mul_sq_le_measure_ball_add
    {m a c₀ h ρ₁ M : ℝ} {σ : ℝ≥0} (hm : 0 < m) (hσ : σ ≠ 0)
    (hlow : ∀ x ∈ A, ∀ ρ ∈ Icc (c₀ * h) ρ₁, m * ρ ^ 2 ≤ μ.real (ball x ρ) + a * ρ ^ 4)
    (hσh : 2 * (c₀ * h) ≤ σ) (hσρ : σ ≤ 2 * ρ₁) (hσa : a * σ ^ 2 ≤ 2 * m) (hM : 0 ≤ M)
    (hAM : μ (thickening (σ / 2 : ℝ) A) ≤ ENNReal.ofReal M) :
    ∃ N : Finset X, (N : Set X) ⊆ A ∧ IsSeparated σ (N : Set X) ∧ IsCover σ A (N : Set X) ∧
      (N.card : ℝ) ≤ 8 * M / (m * σ ^ 2) := by
  have hσ' : (0 : ℝ) < σ := by positivity
  have hfin : μ (thickening (σ / 2 : ℝ) A) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAM
  -- At `ρ = σ / 2` the quartic term is at most half the quadratic one.
  have hball (x : X) (hx : x ∈ A) :
      ENNReal.ofReal (m / 2 * (σ / 2 : ℝ) ^ 2) ≤ μ (ball x (σ / 2 : ℝ)) := by
    have hlt : μ (ball x (σ / 2 : ℝ)) ≠ ∞ := ne_top_of_le_ne_top hfin
      (measure_mono (ball_subset_thickening hx _))
    rw [← ENNReal.ofReal_toReal hlt]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx' := hlow x hx (σ / 2) ⟨by linarith, by linarith⟩
    have hquart : a * (σ / 2 : ℝ) ^ 4 ≤ m / 2 * (σ / 2 : ℝ) ^ 2 := by
      have : a * (σ / 2 : ℝ) ^ 4 = a * σ ^ 2 / 4 * (σ / 2 : ℝ) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    rw [measureReal_def] at hx'
    linarith
  obtain ⟨N, hNA, hN, hNcov, hcard⟩ :=
    exists_finset_isSeparated_isCover_card_le_of_mul_pow_le (by positivity) hσ hM hAM hball
  refine ⟨N, hNA, hN, hNcov, hcard.trans_eq ?_⟩
  field_simp
  ring

end TauCeti
