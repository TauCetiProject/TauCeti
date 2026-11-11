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
vanishing-mesh sequence of partitions of a fixed finite interval. No nesting,
third derivative, derivative growth bound, filtration, or moment bound on the
transformed process is required. Repeated dates and empty grids are allowed.

This is the Taylor-expansion step of Itô's formula. It does not identify the linear
sum as a stochastic integral or the weighted quadratic sum as a time integral.
The proof combines the deterministic compact-path Taylor estimate with Brownian
quadratic-sum convergence, using the subsequence criterion for convergence in measure.
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
vanishes in probability. The grids cover a fixed interval, may repeat dates, and need
not be nested. Only the grid through its last endpoint must be nondecreasing. -/
theorem tendstoInMeasure_sub_sum_taylor_two (hB : IsBrownianReal B P)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {N : ℕ → ℕ} {grid : ℕ → ℕ → ℝ≥0} {a b : ℝ≥0} {δ : ℕ → ℝ}
    (hgrid : ∀ k, MonotoneOn (grid k) (Iic (N k)))
    (ha : ∀ k, grid k 0 = a) (hb : ∀ k, grid k (N k) = b)
    (hmesh : ∀ k i, i < N k → (grid k (i + 1) : ℝ) - grid k i ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ω ↦ f (B b ω) - f (B a ω) -
      (∑ i ∈ Finset.range (N k), deriv f (B (grid k i) ω) *
        (B (grid k (i + 1)) ω - B (grid k i) ω)) -
      1 / 2 * ∑ i ∈ Finset.range (N k), deriv (deriv f) (B (grid k i) ω) *
        (B (grid k (i + 1)) ω - B (grid k i) ω) ^ 2) atTop (fun _ ↦ 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hcoord (t : ℝ≥0) : AEStronglyMeasurable (B t) P :=
    (hB.hasLaw_eval t).aemeasurable.aestronglyMeasurable
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hRmeas (k : ℕ) : AEStronglyMeasurable (fun ω ↦ f (B b ω) - f (B a ω) -
      (∑ i ∈ Finset.range (N k), deriv f (B (grid k i) ω) *
        (B (grid k (i + 1)) ω - B (grid k i) ω)) -
      1 / 2 * ∑ i ∈ Finset.range (N k), deriv (deriv f) (B (grid k i) ω) *
        (B (grid k (i + 1)) ω - B (grid k i) ω) ^ 2) P := by
    have hc := hf.continuous
    have hc' := hf.continuous_deriv (by norm_num)
    have hc'' := hf'.continuous_deriv (by norm_num)
    fun_prop
  have hQ : TendstoInMeasure P (fun k ω ↦ ∑ i ∈ Finset.range (N k),
      (B (grid k (i + 1)) ω - B (grid k i) ω) ^ 2) atTop (fun _ ↦ (b : ℝ) - a) := by
    have h := hB.toIsPreBrownianReal.tendstoInMeasure_quadraticSum
      (grid := fun k (i : Fin (N k + 1)) ↦ grid k i)
      (fun k i j hij ↦ hgrid k (by simpa using i.isLt) (by simpa using j.isLt) hij)
      ha hb (fun k i ↦ hmesh k i i.isLt) hδ
    simp_rw [← Fin.sum_univ_eq_sum_range]
    simpa only [TauCeti.Probability.quadraticSum_def, Fin.val_succ, Fin.val_castSucc] using h
  -- Every subsequence has a further subsequence with bounded quadratic sums on each path.
  apply (exists_seq_tendstoInMeasure_atTop_iff hRmeas).2
  intro ns hns
  obtain ⟨ms, hms, hQae⟩ := (hQ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hB.cont, hQae] with ω hcont hQω
  have hlast (k i : ℕ) (hi : i ≤ N k) : grid k i ≤ b := by
    rw [← hb k]
    exact hgrid k hi (mem_Iic.2 le_rfl) hi
  have hstep (k i : ℕ) (hi : i < N k) : grid k i ≤ grid k (i + 1) :=
    hgrid k hi.le (Nat.succ_le_of_lt hi) (Nat.le_succ i)
  have hlim := TauCeti.tendsto_sub_sum_taylor_two_of_continuousOn hf isCompact_Icc
    (hcont.continuousOn (s := Icc 0 b))
    (t := fun k ↦ grid (ns (ms k))) (n := fun k ↦ N (ns (ms k)))
    (Eventually.of_forall fun k i hi ↦ ⟨bot_le, hlast _ _ hi⟩)
    (Eventually.of_forall fun k i hi ↦ by
      have hd : 0 ≤ (grid (ns (ms k)) (i + 1) : ℝ) - grid (ns (ms k)) i :=
        sub_nonneg.2 (by exact_mod_cast hstep (ns (ms k)) i hi)
      simpa only [NNReal.dist_eq, Real.dist_eq, abs_of_nonneg hd, Function.comp_def] using
        hmesh (ns (ms k)) i hi)
    (hδ.comp (hns.tendsto_atTop.comp hms.tendsto_atTop))
    (hQω.eventually_le_const (by linarith : (b : ℝ) - a < (b : ℝ) - a + 1))
  simpa only [ha, hb] using hlim

end ProbabilityTheory.IsBrownianReal
