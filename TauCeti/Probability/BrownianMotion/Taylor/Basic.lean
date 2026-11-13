/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Partitions
public import TauCeti.Probability.BrownianMotion.Taylor.Parameter

/-!
# Second-order Taylor expansions along Brownian partitions

For a real C² function and Brownian motion, the endpoint increment minus the linear
and quadratic Taylor sums tends to zero in probability along every deterministic
vanishing-mesh family of partitions of a fixed finite interval, indexed by any filter.
The grid conditions need only hold eventually. No nesting,
third derivative, derivative growth bound, filtration, or moment bound on the
transformed process is required. Repeated dates and empty grids are allowed.

This is the Taylor-expansion step of Itô's formula. It does not identify the linear
sum as a stochastic integral or the weighted quadratic sum as a time integral.
Convergence holds in probability; no almost-sure convergence along every partition
sequence is asserted.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The accumulated second-order Taylor error of a C² function along Brownian partitions
vanishes in probability. Eventually, the grids cover a fixed interval and are nondecreasing
through their last endpoint. They may repeat dates and need not be nested.
The family may be indexed by any filter. -/
theorem tendstoInMeasure_sub_sum_taylor_two (hB : IsBrownianReal B P)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0}
    {a b : ℝ≥0} {δ : ι → ℝ}
    (hgrid : ∀ᶠ k in l, MonotoneOn (grid k) (Iic (N k)))
    (ha : ∀ᶠ k in l, grid k 0 = a) (hb : ∀ᶠ k in l, grid k (N k) = b)
    (hmesh : ∀ᶠ k in l, ∀ i < N k, (grid k (i + 1) : ℝ) - grid k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    TendstoInMeasure P (fun k ω ↦ f (B b ω) - f (B a ω) -
      (∑ i ∈ Finset.range (N k), deriv f (B (grid k i) ω) *
        (B (grid k (i + 1)) ω - B (grid k i) ω)) -
      1 / 2 * ∑ i ∈ Finset.range (N k), deriv (deriv f) (B (grid k i) ω) *
        (B (grid k (i + 1)) ω - B (grid k i) ω) ^ 2) l (fun _ ↦ 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let R (k : ι) (ω : Ω) := f (B b ω) - f (B a ω) -
    (∑ i ∈ Finset.range (N k), deriv f (B (grid k i) ω) *
      (B (grid k (i + 1)) ω - B (grid k i) ω)) -
    1 / 2 * ∑ i ∈ Finset.range (N k), deriv (deriv f) (B (grid k i) ω) *
      (B (grid k (i + 1)) ω - B (grid k i) ω) ^ 2
  suffices hlim : TendstoInMeasure P R l (fun _ ↦ (0 : ℝ)) by
    simpa only [R] using hlim
  rw [tendstoInMeasure_iff_tendsto_toNNReal]
  intro ε hε
  by_contra hbad
  obtain ⟨S, hS, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hbad
  -- Failure of convergence supplies bad indices with arbitrarily small mesh and valid grids.
  have hchoose (m : ℕ) : ∃ k,
      (P {ω | ε ≤ edist (R k ω) 0}).toNNReal ∉ S ∧
      MonotoneOn (grid k) (Iic (N k)) ∧ grid k 0 = a ∧ grid k (N k) = b ∧
      (∀ i < N k, (grid k (i + 1) : ℝ) - grid k i ≤ δ k) ∧
      ‖δ k‖ < 1 / (m + 1 : ℝ) := by
    have hsmall := Metric.tendsto_nhds.1 hδ (1 / (m + 1 : ℝ)) (by positivity)
    have hgood := hgrid.and (ha.and (hb.and (hmesh.and hsmall)))
    simpa only [dist_zero_right] using (hfreq.and_eventually hgood).exists
  choose u hu_bad hu_grid hu_a hu_b hu_mesh huδ using hchoose
  have hδu : Tendsto (fun m ↦ δ (u m)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun m ↦ (huδ m).le) tendsto_one_div_add_atTop_nhds_zero_nat
  -- The constant-parameter specialization controls the remainders along this sequence.
  have hRlim : TendstoInMeasure P (fun k ↦ R (u k)) atTop (fun _ ↦ (0 : ℝ)) := by
    have h := hB.tendstoInMeasure_sum_sub_taylorWithinEval_two_param
      (s := {(0 : ℝ)}) isCompact_singleton (f := fun _ ↦ f) (fun _ _ ↦ hf)
      ((hf.continuous_iteratedDeriv 2 (by norm_num)).comp continuous_snd).continuousOn
      (grid := fun k (i : Fin (N (u k) + 1)) ↦ grid (u k) i)
      (fun k i j hij ↦ hu_grid k (by simpa using i.isLt) (by simpa using j.isLt) hij)
      hu_a hu_b (fun k i ↦ hu_mesh k i i.isLt) hδu
      (fun _ _ ↦ 0) (fun _ _ ↦ mem_singleton 0)
    convert h using 1
    funext k ω
    dsimp only [R]
    rw [← hu_b k, ← hu_a k,
      TauCeti.sub_sum_taylor_two_eq_sum_sub_taylorWithinEval f (fun i ↦ B (grid (u k) i) ω)]
    simp only [← Fin.sum_univ_eq_sum_range, Fin.val_succ, Fin.val_castSucc]
  -- Convergence in measure contradicts the choice of every extracted index.
  obtain ⟨m, hm⟩ :=
    ((tendstoInMeasure_iff_tendsto_toNNReal.1 hRlim ε hε).eventually hS).exists
  exact hu_bad m hm

end ProbabilityTheory.IsBrownianReal
