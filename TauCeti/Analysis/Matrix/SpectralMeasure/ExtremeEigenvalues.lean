/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import Mathlib.MeasureTheory.Measure.Support

import TauCeti.MeasureTheory.Measure.Portmanteau

/-!
# Extreme eigenvalues and weak spectral limits

The empirical spectral measure of a Hermitian matrix charges a set exactly when some eigenvalue
lies in it. Consequently, if the empirical spectral measures of a family of Hermitian matrices
converge weakly to a probability measure `μ`, then every point of the support of `μ` is
eventually approximated by eigenvalues. In particular the largest eigenvalue is eventually
larger than any number below a point of the support, and the smallest eigenvalue is eventually
smaller than any number above one.

These are the lower halves of edge limit theorems: weak convergence alone gives
`liminf λ_max ≥ sup (supp μ)` and `limsup λ_min ≤ inf (supp μ)`. The matching upper bounds are
not consequences of weak convergence, since a vanishing proportion of outlying eigenvalues does
not affect the weak limit. The statements are written with eventual strict inequalities rather
than with `liminf` and `limsup`, which on `ℝ` need boundedness side conditions.

## Main statements

* `Matrix.IsHermitian.spectralMeasure_pos_iff`: the spectral measure charges a set if and only if
  some eigenvalue lies in it.
* `Matrix.eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure`: every neighbourhood of
  a point of the support of a weak spectral limit eventually contains an eigenvalue.
* `Matrix.eventually_lt_eigenvalues₀_zero_of_tendsto_spectralMeasure`,
  `Matrix.eventually_eigenvalues₀_card_sub_one_lt_of_tendsto_spectralMeasure`: the largest and
  smallest eigenvalues eventually reach beyond every point of the support.
* `Matrix.tendsto_eigenvalues₀_zero_iff_of_tendsto_spectralMeasure`,
  `Matrix.tendsto_eigenvalues₀_card_sub_one_iff_of_tendsto_spectralMeasure`: convergence of the
  largest or smallest eigenvalue to a point of the support reduces to a one-sided bound.

## References

* Z. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, Chapter 5, where the lower bounds for the extreme eigenvalues are
  derived from the global laws.
-/

public section

open Filter MeasureTheory TauCeti.Probability
open scoped Topology

namespace Matrix

section Single

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [RCLike 𝕜]

/-- The empirical spectral measure of a Hermitian matrix charges a set if and only if some
eigenvalue lies in it. The set need not be measurable. -/
theorem IsHermitian.spectralMeasure_pos_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {s : Set ℝ} :
    0 < (A.spectralMeasure hA : Measure ℝ) s ↔ ∃ k, hA.eigenvalues₀ k ∈ s := by
  rw [spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀,
    empiricalMeasureOfFintype_pos_iff]

end Single

variable {ι 𝕜 : Type*} {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  [∀ i, Nonempty (n i)] [RCLike 𝕜] {l : Filter ι} {A : (i : ι) → Matrix (n i) (n i) 𝕜}
  {hA : ∀ i, (A i).IsHermitian} {μ : ProbabilityMeasure ℝ} {x : ℝ}

/-- If the empirical spectral measures of a family of Hermitian matrices converge weakly to `μ`,
then every neighbourhood of a point of the support of `μ` eventually contains an eigenvalue. -/
theorem eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    (hx : x ∈ (μ : Measure ℝ).support) {U : Set ℝ} (hU : U ∈ 𝓝 x) :
    ∀ᶠ i in l, ∃ k, (hA i).eigenvalues₀ k ∈ U := by
  filter_upwards [ProbabilityMeasure.eventually_measure_pos_of_tendsto_of_mem_support h hx hU]
    with i hi
  exact (hA i).spectralMeasure_pos_iff.1 hi

/-- **Lower bound for the largest eigenvalue from a weak spectral limit.** If the empirical
spectral measures converge weakly to `μ` and `x` lies in the support of `μ`, then for every
`c < x` the largest eigenvalue eventually exceeds `c`. -/
theorem eventually_lt_eigenvalues₀_zero_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    (hx : x ∈ (μ : Measure ℝ).support) {c : ℝ} (hc : c < x) :
    ∀ᶠ i in l, c < (hA i).eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
  filter_upwards [eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h hx
    (Ioi_mem_nhds hc)] with i ⟨k, hk⟩
  exact hk.out.trans_le ((hA i).eigenvalues₀_antitone (Fin.mk_le_mk.2 k.val.zero_le))

/-- **Upper bound for the smallest eigenvalue from a weak spectral limit.** If the empirical
spectral measures converge weakly to `μ` and `x` lies in the support of `μ`, then for every
`c > x` the smallest eigenvalue is eventually below `c`. -/
theorem eventually_eigenvalues₀_card_sub_one_lt_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    (hx : x ∈ (μ : Measure ℝ).support) {c : ℝ} (hc : x < c) :
    ∀ᶠ i in l, (hA i).eigenvalues₀ ⟨Fintype.card (n i) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩
      < c := by
  filter_upwards [eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h hx
    (Iio_mem_nhds hc)] with i ⟨k, hk⟩
  exact ((hA i).eigenvalues₀_antitone (Fin.mk_le_mk.2 (Nat.le_sub_one_of_lt k.isLt))).trans_lt hk

/-- **Edge limits reduce to one-sided bounds.** If the empirical spectral measures converge
weakly to `μ` and `x` lies in the support of `μ`, then the largest eigenvalue tends to `x` if and
only if it is eventually below every `c > x`. -/
theorem tendsto_eigenvalues₀_zero_iff_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    (hx : x ∈ (μ : Measure ℝ).support) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ ⟨0, Fintype.card_pos⟩) l (𝓝 x) ↔
      ∀ c > x, ∀ᶠ i in l, (hA i).eigenvalues₀ ⟨0, Fintype.card_pos⟩ < c :=
  tendsto_order.trans (and_iff_right fun _ hc ↦
    eventually_lt_eigenvalues₀_zero_of_tendsto_spectralMeasure h hx hc)

/-- If the empirical spectral measures converge weakly to `μ` and `x` lies in the support of
`μ`, then the smallest eigenvalue tends to `x` if and only if it eventually exceeds every
`c < x`. -/
theorem tendsto_eigenvalues₀_card_sub_one_iff_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    (hx : x ∈ (μ : Measure ℝ).support) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀
        ⟨Fintype.card (n i) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩) l (𝓝 x) ↔
      ∀ c < x, ∀ᶠ i in l, c < (hA i).eigenvalues₀
        ⟨Fintype.card (n i) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩ :=
  tendsto_order.trans (and_iff_left fun _ hc ↦
    eventually_eigenvalues₀_card_sub_one_lt_of_tendsto_spectralMeasure h hx hc)

end Matrix
