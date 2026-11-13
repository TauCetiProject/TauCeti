/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Partitions
public import TauCeti.Probability.BrownianMotion.QuadraticVariation

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
The proof combines the deterministic compact-path Taylor estimate with Brownian
quadratic-sum convergence, extracting a sequence if convergence in measure fails.
In particular, no almost-sure convergence along every partition sequence is asserted.

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
  have hcoord (t : ℝ≥0) : AEStronglyMeasurable (B t) P :=
    (hB.hasLaw_eval t).aemeasurable.aestronglyMeasurable
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hRmeas (k : ι) : AEStronglyMeasurable (R k) P := by
    dsimp only [R]
    have hc := hf.continuous
    have hc' := hf.continuous_deriv (by norm_num)
    have hc'' := hf'.continuous_deriv (by norm_num)
    refine AEStronglyMeasurable.sub (by fun_prop) ?_
    apply AEStronglyMeasurable.const_mul
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    exact (hc''.comp_aestronglyMeasurable (hcoord (grid k i))).mul
      (((hcoord (grid k (i + 1))).sub (hcoord (grid k i))).pow 2)
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
  -- Quadratic sums along this sequence have an almost-surely convergent subsequence.
  have hQ : TendstoInMeasure P (fun k ω ↦ ∑ i ∈ Finset.range (N (u k)),
      (B (grid (u k) (i + 1)) ω - B (grid (u k) i) ω) ^ 2) atTop
      (fun _ ↦ (b : ℝ) - a) := by
    have h := hB.toIsPreBrownianReal.tendstoInMeasure_quadraticSum
      (grid := fun k (i : Fin (N (u k) + 1)) ↦ grid (u k) i)
      (fun k i j hij ↦ hu_grid k (by simpa using i.isLt) (by simpa using j.isLt) hij)
      hu_a hu_b (fun k i ↦ hu_mesh k i i.isLt) hδu
    simp_rw [← Fin.sum_univ_eq_sum_range]
    simpa only [TauCeti.Probability.quadraticSum_def, Fin.val_succ, Fin.val_castSucc] using h
  obtain ⟨ms, hms, hQae⟩ := hQ.exists_seq_tendsto_ae
  -- On each continuous path, bounded quadratic sums and vanishing mesh control the remainder.
  have hRae : ∀ᵐ ω ∂P, Tendsto (fun k ↦ R (u (ms k)) ω) atTop (𝓝 0) := by
    filter_upwards [hB.cont, hQae] with ω hcont hQω
    have hlast (k i : ℕ) (hi : i ≤ N (u k)) : grid (u k) i ≤ b := by
      rw [← hu_b k]
      exact hu_grid k hi (mem_Iic.2 le_rfl) hi
    have hstep (k i : ℕ) (hi : i < N (u k)) :
        grid (u k) i ≤ grid (u k) (i + 1) :=
      hu_grid k hi.le (Nat.succ_le_of_lt hi) (Nat.le_succ i)
    have hlim := TauCeti.tendsto_sub_sum_taylor_two_of_continuousOn
      (fun _ _ ↦ hf.contDiffAt) isCompact_Icc (hcont.continuousOn (s := Icc 0 b))
      (t := fun k ↦ grid (u (ms k))) (n := fun k ↦ N (u (ms k)))
      (Eventually.of_forall fun k i hi ↦ ⟨bot_le, hlast _ _ hi⟩)
      (Eventually.of_forall fun k i hi ↦ by
        have hd : 0 ≤ (grid (u (ms k)) (i + 1) : ℝ) - grid (u (ms k)) i :=
          sub_nonneg.2 (by exact_mod_cast hstep (ms k) i hi)
        simpa only [NNReal.dist_eq, Real.dist_eq, abs_of_nonneg hd, Function.comp_def] using
          hu_mesh (ms k) i hi)
      (hδu.comp hms.tendsto_atTop)
      (hQω.eventually_le_const (by linarith : (b : ℝ) - a < (b : ℝ) - a + 1))
    simpa only [R, hu_a, hu_b] using hlim
  -- The resulting convergence in measure contradicts the choice of every extracted index.
  have hRlim := tendstoInMeasure_of_tendsto_ae (fun k ↦ hRmeas (u (ms k))) hRae
  obtain ⟨m, hm⟩ :=
    ((tendstoInMeasure_iff_tendsto_toNNReal.1 hRlim ε hε).eventually hS).exists
  exact hu_bad (ms m) hm

end ProbabilityTheory.IsBrownianReal
