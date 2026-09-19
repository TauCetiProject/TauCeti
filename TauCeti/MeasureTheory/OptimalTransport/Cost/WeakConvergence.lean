/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Portmanteau
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Partition

/-!
# Bounded transport costs along weakly convergent marginals

A cost `c : X × X → ℝ≥0∞` that is bounded and vanishes uniformly near the diagonal — for every
`ε > 0` there is `δ > 0` with `c (x, y) ≤ ε` whenever `edist x y < δ` — measures how far apart two
laws are. This file proves that on a separable pseudometric space every such transport cost tends
to `0` along a weakly convergent family of probability measures: if `μᵢ ⇀ μ`, then
`transportCost c μᵢ μ → 0`. Bounded costs such as `min (edist x y) R ^ p` are the truncations
through which the convergence of Wasserstein distances is reduced to weak convergence and the
convergence of moments.

The proof transports mass cell by cell along a finite partition of the space, using the
deterministic estimate `TauCeti.transportCost_le_sum_of_partition`. The cells are the pieces cut
out by finitely many small balls centred at the points of a dense sequence, with radii chosen so
that the limit law does not charge any of the bounding spheres. The masses of such cells converge
by the portmanteau theorem, so the excess mass tends to `0`, while the balls leave only a small
mass of the limit law outside them.

## Main statements

* `TauCeti.tendsto_transportCost_of_tendsto_probabilityMeasure` — a bounded cost vanishing
  uniformly near the diagonal has transport cost tending to `0` along a weakly convergent family.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 6.9, where
  weak convergence together with convergence of moments is shown to give Wasserstein convergence.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, Proposition 7.1.5.
* P. Billingsley, *Convergence of Probability Measures*, 2nd edition, Wiley 1999, Theorem 2.1, the
  portmanteau theorem for sets whose boundary is not charged by the limit law.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section WeakConvergence

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace.SeparableSpace X]

/-- **Bounded transport costs along weak convergence.** On a separable pseudometric space, let
`c : X × X → ℝ≥0∞` be a bounded cost vanishing uniformly near the diagonal: for every `ε > 0`
there is `δ > 0` such that `c (x, y) ≤ ε` whenever `edist x y < δ`. If probability measures `μᵢ`
converge weakly to `μ`, then the transport cost of `c` from `μᵢ` to `μ` tends to `0`. -/
theorem tendsto_transportCost_of_tendsto_probabilityMeasure {c : X × X → ℝ≥0∞} {M : ℝ≥0∞}
    (hM_top : M ≠ ∞) (hM : ∀ z, c z ≤ M)
    (hc : ∀ ε > 0, ∃ δ > 0, ∀ x y, edist x y < δ → c (x, y) ≤ ε)
    {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (h : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i ↦ transportCost c (μs i : Measure X) (μ : Measure X)) L (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top
  obtain ⟨δ, hδ, hcδ⟩ := hc (ε / 3) hε3
  obtain ⟨r, -, hr, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  rw [ENNReal.ofReal_pos] at hr
  -- A partition whose last cell carries mass at most `ε / (3 M)` for the limit law, so that the
  -- cost of the last cell is at most `ε / 3`.
  obtain ⟨κ, hκ, hMκ⟩ : ∃ κ > 0, M * κ ≤ ε / 3 :=
    ⟨ε / 3 / M, ENNReal.div_pos hε3.ne' hM_top, ENNReal.mul_div_le⟩
  obtain ⟨N, A, hAm, hAd, hAu, hAf, hAball, hAlast⟩ :=
    (μ : Measure X).exists_partition_null_frontier_small_last (half_pos hr) hκ
  set η : Fin (N + 1) → ℝ≥0∞ := fun i ↦ if i = Fin.last N then M else ε / 3 with hη
  have hcA (i : Fin (N + 1)) : ∀ x ∈ A i, ∀ y ∈ A i, c (x, y) ≤ η i := by
    intro x hx y hy
    by_cases hi : i = Fin.last N
    · simpa [hη, hi] using hM (x, y)
    · obtain ⟨z, hz⟩ := hAball i hi
      simp only [hη, hi, ite_false]
      refine hcδ x y (lt_of_lt_of_le ?_ hrδ.le)
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr]
      have := (dist_triangle x z y).trans_lt
        (add_lt_add (Metric.mem_ball.1 (hz hx)) (Metric.mem_ball'.1 (hz hy)))
      linarith
  -- The weighted cell costs of the limit law are at most `2 ε / 3`.
  have hsum : ∑ i, η i * (μ : Measure X) (A i) ≤ ε / 3 + ε / 3 := by
    have hsplit (i : Fin (N + 1)) : η i * (μ : Measure X) (A i) ≤
        ε / 3 * (μ : Measure X) (A i) +
          if i = Fin.last N then M * (μ : Measure X) (A i) else 0 := by
      by_cases hi : i = Fin.last N <;> simp [hη, hi]
    calc ∑ i, η i * (μ : Measure X) (A i)
        ≤ ∑ i, (ε / 3 * (μ : Measure X) (A i) +
            if i = Fin.last N then M * (μ : Measure X) (A i) else 0) :=
          Finset.sum_le_sum fun i _ ↦ hsplit i
      _ = ε / 3 * (μ : Measure X) univ + M * (μ : Measure X) (A (Fin.last N)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ,
            ← tsum_fintype (L := .unconditional _), ← measure_iUnion hAd hAm, hAu]
          simp only [Finset.mem_univ, ite_true]
      _ ≤ ε / 3 + ε / 3 := by
          rw [measure_univ, mul_one]
          gcongr
          exact (mul_le_mul_right hAlast M).trans hMκ
  -- The excess mass tends to `0` by the portmanteau theorem for cells with null boundary.
  have hexcess : Tendsto (fun j ↦ M * ∑ i, ((μs j : Measure X) (A i) - (μ : Measure X) (A i)))
      L (𝓝 0) := by
    have hcell (i : Fin (N + 1)) : Tendsto
        (fun j ↦ (μs j : Measure X) (A i) - (μ : Measure X) (A i)) L (𝓝 0) := by
      simpa using ENNReal.Tendsto.sub
        (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h (hAf i))
        (tendsto_const_nhds (x := (μ : Measure X) (A i))) (Or.inl (measure_ne_top _ _))
    simpa using ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun i _ ↦ hcell i)
      (Or.inr hM_top)
  filter_upwards [hexcess.eventually (ge_mem_nhds hε3)] with j hj
  calc transportCost c (μs j : Measure X) (μ : Measure X)
      ≤ ∑ i, η i * (μ : Measure X) (A i) +
          M * ∑ i, ((μs j : Measure X) (A i) - (μ : Measure X) (A i)) :=
        transportCost_le_sum_of_partition hAm hAm hAd hAd hAu hAu hcA hM _ _ (by simp)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add hsum hj
    _ = ε := ENNReal.add_thirds ε

end WeakConvergence

end TauCeti
