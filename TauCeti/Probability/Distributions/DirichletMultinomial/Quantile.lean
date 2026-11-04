/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Probability.Distributions.BetaBinomial.Quantile
public import TauCeti.Probability.Distributions.DirichletMultinomial.Aggregation
public import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of Dirichlet-multinomial coordinates

With at least two categories, a coordinate of a Dirichlet-multinomial count vector has a
beta-binomial law. Its real-cast quantile therefore has the scalar beta-binomial crossing
characterization. With one category, all trials instead fall in that category, so its quantile is
constantly the trial count.

This file also records the one-sided endpoint limits. The lower endpoint is zero except in the
one-category case, while the upper endpoint is always the trial count.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 40.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι] {a : ι → ℝ}

/-- For at least two categories, the real-cast quantile of a Dirichlet-multinomial coordinate is
the quantile of its beta-binomial marginal. -/
theorem quantile_map_cast_eval_dirichletMultinomialMeasure [DecidableEq ι] [Nontrivial ι]
    (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) (u : ℝ) :
    ((dirichletMultinomialMeasure n a).map (fun k ↦ (k i : ℝ))).quantile u =
      ((betaBinomialMeasure n (a i) (∑ j with j ≠ i, a j)).map
        (Nat.cast : ℕ → ℝ)).quantile u := by
  -- Expose the cast as a composition for the reverse `Measure.map_map` rewrite.
  rw [show (fun k : ι → ℕ ↦ (k i : ℝ)) =
      (Nat.cast : ℕ → ℝ) ∘ fun k ↦ k i by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    map_eval_dirichletMultinomialMeasure ha n i]

/-- For at least two categories, a natural number is the coordinate quantile exactly when it is
the least count whose beta-binomial cumulative mass reaches the level. -/
theorem quantile_map_cast_eval_dirichletMultinomialMeasure_eq_iff [DecidableEq ι]
    [Nontrivial ι] (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) {u : ℝ}
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((dirichletMultinomialMeasure n a).map (fun x ↦ (x i : ℝ))).quantile u = k ↔
      IsLeast {m : ℕ | u ≤ ∑ j ∈ Finset.Iic m,
        n.choose j * beta (a i + j) ((∑ l with l ≠ i, a l) + (n - j)) /
          beta (a i) (∑ l with l ≠ i, a l)} k := by
  rw [quantile_map_cast_eval_dirichletMultinomialMeasure ha n i,
    quantile_map_cast_betaBinomialMeasure_eq_iff (ha i) (Finset.sum_filter_ne_pos ha i) hu]

/-- With one category, every coordinate quantile at a level in `(0, 1]` is the trial count. -/
@[simp]
theorem quantile_map_cast_eval_dirichletMultinomialMeasure_of_card_eq_one
    (ha : ∀ i, 0 < a i) (hcard : Fintype.card ι = 1) (n : ℕ) (i : ι)
    {u : ℝ} (hu : u ∈ Ioc 0 1) :
    ((dirichletMultinomialMeasure n a).map (fun k ↦ (k i : ℝ))).quantile u = n := by
  let _ : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  rw [dirichletMultinomialMeasure_eq_dirac_of_subsingleton ha n,
    Measure.map_dirac' (by fun_prop), Measure.quantile_dirac _ hu.1 hu.2]

/-- At level zero, a Dirichlet-multinomial coordinate quantile tends to zero, except for the
one-category law where it remains the trial count. -/
theorem tendsto_quantile_map_cast_eval_dirichletMultinomialMeasure_nhdsGT_zero
    (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    Tendsto (fun u ↦
      (((dirichletMultinomialMeasure n a).map (fun k ↦ (k i : ℝ))).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if Fintype.card ι = 1 then (n : EReal) else 0)) := by
  classical
  rcases subsingleton_or_nontrivial ι with _ | _
  · let _ : Unique ι := uniqueOfSubsingleton i
    have hcard : Fintype.card ι = 1 := Fintype.card_unique
    simp only [hcard, ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (α := ℝ) zero_lt_one] with u hu
    rw [quantile_map_cast_eval_dirichletMultinomialMeasure_of_card_eq_one ha hcard n i
      ⟨hu.1, hu.2.le⟩]
    norm_cast
  · -- Expose the cast as a composition for the reverse `Measure.map_map` rewrite.
    rw [ite_eq_right (ne_of_gt Fintype.one_lt_card),
      show (fun k : ι → ℕ ↦ (k i : ℝ)) =
        (Nat.cast : ℕ → ℝ) ∘ fun k ↦ k i by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      map_eval_dirichletMultinomialMeasure ha n i]
    exact tendsto_quantile_map_cast_betaBinomialMeasure_nhdsGT_zero
      (ha i) (Finset.sum_filter_ne_pos ha i) n

/-- At level one, every valid Dirichlet-multinomial coordinate quantile tends to the trial
count. -/
theorem tendsto_quantile_map_cast_eval_dirichletMultinomialMeasure_nhdsLT_one
    (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    Tendsto (fun u ↦
      (((dirichletMultinomialMeasure n a).map (fun k ↦ (k i : ℝ))).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (n : EReal)) := by
  classical
  rcases subsingleton_or_nontrivial ι with _ | _
  · let _ : Unique ι := uniqueOfSubsingleton i
    have hcard : Fintype.card ι = 1 := Fintype.card_unique
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT (α := ℝ) zero_lt_one] with u hu
    rw [quantile_map_cast_eval_dirichletMultinomialMeasure_of_card_eq_one ha hcard n i
      ⟨hu.1, hu.2.le⟩]
    norm_cast
  · -- Expose the cast as a composition for the reverse `Measure.map_map` rewrite.
    rw [show (fun k : ι → ℕ ↦ (k i : ℝ)) =
        (Nat.cast : ℕ → ℝ) ∘ fun k ↦ k i by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      map_eval_dirichletMultinomialMeasure ha n i]
    exact tendsto_quantile_map_cast_betaBinomialMeasure_nhdsLT_one
      (ha i) (Finset.sum_filter_ne_pos ha i) n

end TauCeti.Probability
