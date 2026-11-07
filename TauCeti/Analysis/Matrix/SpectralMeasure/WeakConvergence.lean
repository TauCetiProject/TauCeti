/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.RankPerturbation
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf

/-!
# Weak spectral limits under low-rank perturbations

Hermitian matrix families whose difference has rank negligible compared with their dimension
have the same weak spectral limits. In particular, adding a uniformly bounded-rank Hermitian
matrix preserves a weak spectral limit as the dimension tends to infinity. There is no bound on
the operator norm of the perturbation and no atomlessness assumption on the limiting measure.
This allows truncations and finite-rank spikes to be removed when proving global spectral laws;
it does not assert stability of extreme eigenvalues.

The index types of the matrices may vary, and convergence is along any countably generated
filter. Applied at each sample point, the results also preserve almost-sure weak spectral limits
without any independence assumption across dimensions.

## References

* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices* (2010),
  Theorem A.43 (the rank inequality).
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Matrix

variable {ι 𝕜 : Type*} {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  [∀ i, Nonempty (n i)] [RCLike 𝕜] {l : Filter ι} [l.IsCountablyGenerated]
  {μ : ProbabilityMeasure ℝ}

/-- A perturbation whose rank divided by the matrix dimension tends to zero preserves, in both
directions, weak convergence of the empirical spectral measures. The limiting law may have
atoms, and the perturbation need not have bounded operator norm. -/
theorem tendsto_spectralMeasure_iff_of_rank_sub_div_card_tendsto_zero
    (A B : (i : ι) → Matrix (n i) (n i) 𝕜)
    (hA : ∀ i, (A i).IsHermitian) (hB : ∀ i, (B i).IsHermitian)
    (hrank : Tendsto (fun i ↦ ((A i - B i).rank : ℝ) / Fintype.card (n i)) l (𝓝 0)) :
    Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ) ↔
      Tendsto (fun i ↦ (B i).spectralMeasure (hB i)) l (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_continuousAt_tendsto_cdf,
    ProbabilityMeasure.tendsto_iff_forall_continuousAt_tendsto_cdf]
  have hdist (t : ℝ) :
      Tendsto (fun i ↦ dist (cdf ((A i).spectralMeasure (hA i) : Measure ℝ) t)
        (cdf ((B i).spectralMeasure (hB i) : Measure ℝ) t)) l (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ ?_) hrank
    simpa only [Real.dist_eq, cdf_eq_real] using
      (hA i).abs_spectralMeasure_Iic_sub_le_rank_div_card (hB i) t
  exact forall_congr' fun t ↦ forall_congr' fun _ ↦ tendsto_iff_of_dist (hdist t)

/-- Adding Hermitian matrices of eventually uniformly bounded rank does not change a weak
spectral limit when the dimensions tend to infinity. In particular, the sizes of the nonzero
eigenvalues of the perturbations are unrestricted. -/
theorem tendsto_spectralMeasure_add_iff_of_rank_le
    (A P : (i : ι) → Matrix (n i) (n i) 𝕜)
    (hA : ∀ i, (A i).IsHermitian) (hP : ∀ i, (P i).IsHermitian)
    (hdim : Tendsto (fun i ↦ Fintype.card (n i)) l atTop)
    {r : ℕ} (hrank : ∀ᶠ i in l, (P i).rank ≤ r) :
    Tendsto (fun i ↦ (A i + P i).spectralMeasure ((hA i).add (hP i))) l (𝓝 μ) ↔
      Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ) := by
  apply tendsto_spectralMeasure_iff_of_rank_sub_div_card_tendsto_zero
  simp only [add_sub_cancel_left]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_
    ((tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)).comp hdim)
  filter_upwards [hrank] with i hi
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hi) (Nat.cast_nonneg _)

end Matrix
