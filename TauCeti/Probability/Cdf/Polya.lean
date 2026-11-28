/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf
public import TauCeti.Probability.Cdf.KolmogorovDist
public import TauCeti.Probability.Quantile

/-!
# Pólya's theorem

Weak convergence of probability measures on `ℝ` to a law with continuous distribution function is
uniform convergence of the distribution functions, that is, convergence in the Kolmogorov distance.

The deterministic heart of the argument is a finite grid: if `cdf ν` is continuous, then for every
`ε > 0` there are finitely many points such that a discrepancy of at most `δ` between `cdf μ` and
`cdf ν` at these points forces `kolmogorovDist μ ν ≤ δ + ε`, for every measure `μ` at once. The
grid consists of the quantiles of `ν` at the levels `j / K`, `0 < j < K`, with `1 / K ≤ ε`; between
two consecutive grid points both distribution functions are monotone and `cdf ν` rises by `1 / K`.
Pointwise convergence at the finitely many grid points is therefore uniform convergence. Combined
with the Helly–Bray theorem
`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_continuousAt_tendsto_cdf` this gives Pólya's
theorem. The converse direction, from convergence in the Kolmogorov distance to weak convergence,
needs no continuity: uniform convergence of distribution functions implies pointwise convergence.

These results are what make the Kolmogorov distance the natural measure of the error of normal
approximations: a limit theorem in law with a continuous limit is automatically uniform in the
argument of the distribution function.

## Main results

* `ProbabilityTheory.exists_finset_kolmogorovDist_le_add`: for a continuous `cdf ν`, a finite grid
  controls the Kolmogorov distance to `ν` up to an arbitrary `ε > 0`.
* `ProbabilityTheory.tendsto_kolmogorovDist_iff_forall_tendsto_cdf`: for a continuous `cdf ν`,
  convergence in the Kolmogorov distance to `ν` is pointwise convergence of distribution functions.
* `ProbabilityTheory.tendsto_cdf_of_tendsto_kolmogorovDist`: convergence in the Kolmogorov distance
  implies pointwise convergence of distribution functions, with no continuity hypothesis.
* `MeasureTheory.ProbabilityMeasure.tendsto_kolmogorovDist_of_tendsto`: weak convergence to a
  law with continuous distribution function implies convergence in the Kolmogorov distance.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_kolmogorovDist`: convergence in the
  Kolmogorov distance implies weak convergence along a countably generated filter.
* `MeasureTheory.ProbabilityMeasure.tendsto_kolmogorovDist_iff_tendsto`: **Pólya's theorem**.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Lemma 2.11.
* G. Pólya, *Über den zentralen Grenzwertsatz der Wahrscheinlichkeitsrechnung und das
  Momentenproblem*, Math. Z. 8 (1920), 171–181.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

/-- Using the grid point at level `j / K` with `j = ⌊K · cdf ν t⌋₊ + 1`, which lies at or above
`t`, the discrepancy `cdf μ t - cdf ν t` exceeds the discrepancy at the grid point by at most
`1 / K`. When no such grid point exists, `cdf ν t ≥ 1 - 1 / K` and the bound `cdf μ t ≤ 1`
suffices. -/
private theorem cdf_sub_cdf_le_of_grid {μ ν : Measure ℝ} (hν : Continuous (cdf ν)) {K : ℕ}
    (hK : 0 < K) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ j ∈ Finset.Ioo 0 K, |cdf μ (ν.quantile (j / K)) - cdf ν (ν.quantile (j / K))| ≤ δ)
    (t : ℝ) : cdf μ t - cdf ν t ≤ δ + 1 / K := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  set u := cdf ν t
  have hu0 : 0 ≤ u := cdf_nonneg ν t
  rcases le_or_gt ((K - 1 : ℝ) / K) u with hu | hu
  · -- Near the top `cdf ν t ≥ 1 - 1 / K`, and `cdf μ t ≤ 1`.
    have : (K - 1 : ℝ) / K = 1 - 1 / K := by field_simp
    linarith [cdf_le_one μ t]
  -- Otherwise the next grid level `j / K` lies strictly above `u` and at most `1 / K` above it.
  set j := ⌊K * u⌋₊ + 1 with hj
  have hKu : K * u < K - 1 := by rwa [lt_div_iff₀ hK', mul_comm] at hu
  have hfloor : (⌊K * u⌋₊ : ℝ) ≤ K * u := Nat.floor_le (by positivity)
  have hjK : j < K := by
    have : (j : ℝ) < K := by push_cast [hj]; linarith
    exact_mod_cast this
  have hjpos : 0 < (j : ℝ) / K := by positivity
  have hj1 : (j : ℝ) / K < 1 := (div_lt_one hK').2 (by exact_mod_cast hjK)
  have hcdfj : cdf ν (ν.quantile (j / K)) = j / K := Measure.cdf_quantile ν hν hjpos hj1
  have hlt : u < j / K := by
    rw [lt_div_iff₀ hK', mul_comm]
    push_cast [hj]
    exact Nat.lt_floor_add_one _
  have hle : (j : ℝ) / K - u ≤ 1 / K := by
    rw [div_sub' hK'.ne', div_le_div_iff_of_pos_right hK']
    push_cast [hj]
    linarith
  -- The grid point lies to the right of `t`, so `cdf μ t` is at most its value there.
  have htq : t ≤ ν.quantile (j / K) := by
    by_contra! hq
    exact (hcdfj ▸ (cdf ν).mono hq.le).not_gt hlt
  have hμ := (cdf μ).mono htq
  have hgrid := (abs_le.1 (h j (Finset.mem_Ioo.2 ⟨by omega, hjK⟩))).2
  linarith

/-- Using the grid point at level `j / K` with `j = ⌈K · cdf ν t⌉₊ - 1`, which lies at or below
`t`, the discrepancy `cdf ν t - cdf μ t` exceeds the discrepancy at the grid point by at most
`1 / K`. When no such grid point exists, `cdf ν t ≤ 1 / K` and the bound `cdf μ t ≥ 0` suffices. -/
private theorem cdf_sub_cdf_le_of_grid' {μ ν : Measure ℝ} (hν : Continuous (cdf ν)) {K : ℕ}
    (hK : 0 < K) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ j ∈ Finset.Ioo 0 K, |cdf μ (ν.quantile (j / K)) - cdf ν (ν.quantile (j / K))| ≤ δ)
    (t : ℝ) : cdf ν t - cdf μ t ≤ δ + 1 / K := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  set u := cdf ν t
  rcases le_or_gt u (1 / K) with hu | hu
  · -- Near the bottom `cdf ν t ≤ 1 / K`, and `cdf μ t ≥ 0`.
    linarith [cdf_nonneg μ t]
  -- Otherwise the previous grid level `j / K` lies strictly below `u` and at most `1 / K` below.
  have hKu : 1 < K * u := by rwa [div_lt_iff₀ hK', mul_comm] at hu
  have hceil1 : 1 < ⌈K * u⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hKu)
  have hceilK : ⌈K * u⌉₊ ≤ K := Nat.ceil_le.2 (by nlinarith [cdf_le_one ν t])
  set j := ⌈K * u⌉₊ - 1 with hj
  have hjcast : (j : ℝ) = ⌈K * u⌉₊ - 1 := by rw [hj, Nat.cast_sub hceil1.le, Nat.cast_one]
  have hjK : j < K := by omega
  have hjpos : 0 < (j : ℝ) / K := div_pos (by exact_mod_cast (show 0 < j by omega)) hK'
  have hj1 : (j : ℝ) / K < 1 := (div_lt_one hK').2 (by exact_mod_cast hjK)
  have hcdfj : cdf ν (ν.quantile (j / K)) = j / K := Measure.cdf_quantile ν hν hjpos hj1
  have hlt : (j : ℝ) / K < u := by
    rw [div_lt_iff₀ hK', mul_comm, hjcast]
    linarith [Nat.ceil_lt_add_one (show 0 ≤ (K : ℝ) * u by positivity)]
  have hle : u - (j : ℝ) / K ≤ 1 / K := by
    rw [sub_div' hK'.ne', div_le_div_iff_of_pos_right hK', hjcast]
    linarith [Nat.le_ceil ((K : ℝ) * u)]
  -- The grid point lies to the left of `t`, so `cdf μ t` is at least its value there.
  have hqt : ν.quantile (j / K) ≤ t := by
    by_contra! hq
    exact (hcdfj ▸ (cdf ν).mono hq.le).not_gt hlt
  have hμ := (cdf μ).mono hqt
  have hgrid := (abs_le.1 (h j (Finset.mem_Ioo.2 ⟨by omega, hjK⟩))).1
  linarith

/-- **Finite grid for the Kolmogorov distance.** If the distribution function of `ν` is
continuous, then for every `ε > 0` there is a finite set of points such that, for every measure
`μ`, a discrepancy of at most `δ` between `cdf μ` and `cdf ν` on that set forces
`kolmogorovDist μ ν ≤ δ + ε`. -/
theorem exists_finset_kolmogorovDist_le_add {ν : Measure ℝ} (hν : Continuous (cdf ν)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s : Finset ℝ, ∀ (μ : Measure ℝ) {δ : ℝ}, 0 ≤ δ →
      (∀ t ∈ s, |cdf μ t - cdf ν t| ≤ δ) → kolmogorovDist μ ν ≤ δ + ε := by
  obtain ⟨K, hKε⟩ := exists_nat_one_div_lt hε
  refine ⟨(Finset.Ioo 0 (K + 1)).image fun j : ℕ ↦ ν.quantile (j / (K + 1 : ℕ)),
    fun μ δ hδ h ↦ ?_⟩
  have hgrid : ∀ j ∈ Finset.Ioo 0 (K + 1),
      |cdf μ (ν.quantile (j / (K + 1 : ℕ))) - cdf ν (ν.quantile (j / (K + 1 : ℕ)))| ≤ δ :=
    fun j hj ↦ h _ (Finset.mem_image_of_mem _ hj)
  have hKε' : 1 / ((K + 1 : ℕ) : ℝ) ≤ ε := by exact_mod_cast hKε.le
  refine kolmogorovDist_le fun t ↦ abs_sub_le_iff.2 ⟨?_, ?_⟩
  · linarith [cdf_sub_cdf_le_of_grid hν K.succ_pos hδ hgrid t]
  · linarith [cdf_sub_cdf_le_of_grid' hν K.succ_pos hδ hgrid t]

variable {ι : Type*} {l : Filter ι}

/-- Convergence in the Kolmogorov distance implies pointwise convergence of the distribution
functions. No continuity of the limiting distribution function is needed. -/
theorem tendsto_cdf_of_tendsto_kolmogorovDist {μ : ι → Measure ℝ} {ν : Measure ℝ}
    (h : Tendsto (fun i ↦ kolmogorovDist (μ i) ν) l (𝓝 0)) (t : ℝ) :
    Tendsto (fun i ↦ cdf (μ i) t) l (𝓝 (cdf ν t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun i ↦ abs_cdf_sub_cdf_le_kolmogorovDist (μ i) ν t) h

/-- If the distribution function of `ν` is continuous, pointwise convergence of distribution
functions to it is convergence in the Kolmogorov distance. -/
theorem tendsto_kolmogorovDist_of_forall_tendsto_cdf {μ : ι → Measure ℝ} {ν : Measure ℝ}
    (hν : Continuous (cdf ν)) (h : ∀ t, Tendsto (fun i ↦ cdf (μ i) t) l (𝓝 (cdf ν t))) :
    Tendsto (fun i ↦ kolmogorovDist (μ i) ν) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨s, hs⟩ := exists_finset_kolmogorovDist_le_add hν (half_pos hε)
  have hev : ∀ᶠ i in l, ∀ t ∈ s, |cdf (μ i) t - cdf ν t| ≤ ε / 4 :=
    (eventually_all_finset s).2 fun t _ ↦
      ((Metric.tendsto_nhds.1 (h t)) (ε / 4) (by positivity)).mono fun _ hi ↦ hi.le
  filter_upwards [hev] with i hi
  have := hs (μ i) (by positivity) hi
  rw [Real.dist_0_eq_abs, abs_of_nonneg (kolmogorovDist_nonneg _ _)]
  linarith

/-- **Kolmogorov distance and pointwise convergence.** If the distribution function of `ν` is
continuous, convergence to `ν` in the Kolmogorov distance is equivalent to pointwise convergence
of the distribution functions. -/
theorem tendsto_kolmogorovDist_iff_forall_tendsto_cdf {μ : ι → Measure ℝ} {ν : Measure ℝ}
    (hν : Continuous (cdf ν)) :
    Tendsto (fun i ↦ kolmogorovDist (μ i) ν) l (𝓝 0) ↔
      ∀ t, Tendsto (fun i ↦ cdf (μ i) t) l (𝓝 (cdf ν t)) :=
  ⟨tendsto_cdf_of_tendsto_kolmogorovDist, tendsto_kolmogorovDist_of_forall_tendsto_cdf hν⟩

end ProbabilityTheory

namespace MeasureTheory.ProbabilityMeasure

open ProbabilityTheory

variable {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}

/-- Weak convergence of probability measures on `ℝ` to a law with continuous distribution
function implies convergence in the Kolmogorov distance. -/
theorem tendsto_kolmogorovDist_of_tendsto (hμ : Continuous (cdf (μ : Measure ℝ)))
    (h : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun i ↦ kolmogorovDist (μs i) μ) l (𝓝 0) :=
  tendsto_kolmogorovDist_of_forall_tendsto_cdf hμ fun _ ↦
    tendsto_cdf_of_tendsto_of_continuousAt h hμ.continuousAt

/-- Convergence of probability measures on `ℝ` in the Kolmogorov distance implies weak
convergence along any countably generated filter, whatever the limiting law. -/
theorem tendsto_of_tendsto_kolmogorovDist [l.IsCountablyGenerated]
    (h : Tendsto (fun i ↦ kolmogorovDist (μs i) μ) l (𝓝 0)) : Tendsto μs l (𝓝 μ) :=
  tendsto_iff_forall_continuousAt_tendsto_cdf.2 fun t _ ↦
    tendsto_cdf_of_tendsto_kolmogorovDist h t

/-- **Pólya's theorem.** Along a countably generated filter, probability measures on `ℝ` converge
weakly to a law with continuous distribution function if and only if they converge to it in the
Kolmogorov distance, that is, their distribution functions converge uniformly. -/
theorem tendsto_kolmogorovDist_iff_tendsto [l.IsCountablyGenerated]
    (hμ : Continuous (cdf (μ : Measure ℝ))) :
    Tendsto (fun i ↦ kolmogorovDist (μs i) μ) l (𝓝 0) ↔ Tendsto μs l (𝓝 μ) :=
  ⟨tendsto_of_tendsto_kolmogorovDist, tendsto_kolmogorovDist_of_tendsto hμ⟩

end MeasureTheory.ProbabilityMeasure
