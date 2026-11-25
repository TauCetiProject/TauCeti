/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.QuadraticVariation.Basic
public import TauCeti.Probability.BrownianMotion.WeightedQuadraticVariation.Basic
public import TauCeti.Probability.Process.Stratonovich
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Calculus.Taylor.Symmetric
import TauCeti.Data.Stream.Init
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Order.Monotone.Basic

/-!
# Brownian Stratonovich symmetric-endpoint and temporal-midpoint partition limits

Along deterministic partitions of `[a, b]` with vanishing mesh, two discrete approximations to the
Stratonovich integral of a `C¹` function `h` with primitive `H` along Brownian motion `B` converge
in probability to `H(B_b) - H(B_a)` without any second derivative of `h` or moment assumption on
`h(B)` or `H(B)`:

* **Symmetric-endpoint sums**
  (`IsBrownianReal.tendstoInMeasure_sum_half_add_mul_sub`):
  `∑ (h(B_{t_i}) + h(B_{t_{i+1}})) / 2 * (B_{t_{i+1}} - B_{t_i}) → H(B_b) - H(B_a)` in probability.
  Because this follows from path continuity and unweighted quadratic-sum convergence alone, the
  same limit holds for `B + A` when `A` has continuous bounded-variation paths
  (`IsBrownianReal.tendstoInMeasure_sum_half_add_mul_sub_add_of_boundedVariationOn`).
* **Temporal-midpoint sums**
  (`IsBrownianReal.tendstoInMeasure_sum_midpoint_mul_sub`):
  `∑ h(B_{(t_i + t_{i+1}) / 2}) * (B_{t_{i+1}} - B_{t_i}) → H(B_b) - H(B_a)` in probability.
  Comparing the midpoint sample with the symmetric endpoint average isolates the alternating
  half-step quadratic sum
  `1 / 2 * ∑ h'(B_{t_i}) * ((B_{m_i} - B_{t_i})² - (B_{t_{i+1}} - B_{m_i})²)`,
  whose `L²` norm is computed exactly on predictable and bounded left weights
  (`TauCeti.Probability.IsFilteredPreBrownianReal.integral_sq_sum_mul_midpoint_sq_sub_sq`,
  `IsPreBrownianReal.integral_sq_sum_comp_mul_midpoint_sq_sub_sq`) and extended
  to general continuous `h'` by pathwise localization on `[a, b]`
  (`IsBrownianReal.tendstoInMeasure_sum_mul_midpoint_sq_sub_sq`).

In contrast to the symmetric-endpoint rule, temporal-midpoint convergence genuinely depends on the
Brownian half-step increment law: for a deterministically time-changed pre-Brownian motion `B ∘ A`
evaluated at intermediate clock values `a_i ≤ c_i ≤ a_{i+1}`, the deviation
`(∑ B(c_i)(B(a_{i+1}) - B(a_i))) - (B(a_n)² - B(a_0)²) / 2` of the intermediate-sample sum from
the symmetric Stratonovich value has exact expectation `1 / 2 * ∑ ((c_i - a_i) - (a_{i+1} - c_i))`
and variance `1 / 2 * ∑ ((c_i - a_i)² + (a_{i+1} - c_i)²)`
(`IsPreBrownianReal.integral_sum_comp_midpoint_mul_sub_sub_half_sq`,
`IsPreBrownianReal.variance_sum_comp_midpoint_mul_sub_sub_half_sq`,
`IsPreBrownianReal.variance_sum_comp_midpoint_mul_sub_sub_half_sq_le`), so under
vanishing clock mesh and asymptotic clock asymmetry `β` the intermediate-sample sum converges in
probability to `(B(A_1)² - B(A_0)²) / 2 + β`
(`IsPreBrownianReal.tendstoInMeasure_sum_comp_midpoint_mul_sub`).

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter V, §5.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

noncomputable section

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

private lemma monotoneOn_interleave_midpoint {n : ℕ} {t : ℕ → ℝ≥0}
    (ht : MonotoneOn t (Set.Iic n)) :
    MonotoneOn (TauCeti.interleave t fun i ↦ (t i + t (i + 1)) / 2) (Set.Iic (2 * n)) :=
  TauCeti.monotoneOn_interleave_Iic fun i hi ↦ by
    have hle := ht hi.le hi (Nat.le_succ _)
    exact ⟨TauCeti.left_le_add_div_two.2 hle, TauCeti.add_div_two_le_right.2 hle⟩

private lemma interleave_midpoint_step_le {n : ℕ} {t : ℕ → ℝ≥0} {δ : ℝ}
    (ht : MonotoneOn t (Set.Iic n)) (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ)
    {j : ℕ} (hj : j < 2 * n) :
    ((TauCeti.interleave t (fun i ↦ (t i + t (i + 1)) / 2) (j + 1) : ℝ≥0) : ℝ) -
      ((TauCeti.interleave t (fun i ↦ (t i + t (i + 1)) / 2) j : ℝ≥0) : ℝ) ≤ δ :=
  (TauCeti.forall_lt_two_mul_interleave_succ_iff
    (R := fun _ (x y : ℝ≥0) ↦ (y : ℝ) - x ≤ δ)).2 (fun i hi ↦ by
      have hle : (t i : ℝ) ≤ t (i + 1) := NNReal.coe_le_coe.2 (ht hi.le hi (Nat.le_succ _))
      constructor <;> (push_cast; linarith [hmesh i hi])) j hj

private lemma grid_mem_Icc {a b : ℝ≥0} {k : ℕ} {π : ℕ → ℝ≥0}
    (hmono : MonotoneOn π (Set.Iic k)) (ha : π 0 = a) (hb : π k = b) {i : ℕ} (hi : i ≤ k) :
    π i ∈ Icc a b :=
  ha ▸ hb ▸ (hmono.mono Icc_subset_Iic_self).mapsTo_Icc ⟨Nat.zero_le _, hi⟩

private lemma grid_dist_le {k : ℕ} {π : ℕ → ℝ≥0} {δ : ℝ}
    (hmono : MonotoneOn π (Set.Iic k)) {i : ℕ} (hi : i < k)
    (hmesh : (π (i + 1) : ℝ) - π i ≤ δ) :
    dist (π (i + 1)) (π i) ≤ δ := by
  rw [NNReal.dist_eq, abs_of_nonneg
    (sub_nonneg.2 (NNReal.coe_le_coe.2 (hmono hi.le hi (Nat.le_succ _))))]
  exact hmesh

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- For square-integrable heights `Y i` measurable at `t i`, weighting the difference of squared
half-step Brownian increments
`(B((t_i + t_{i+1}) / 2) - B(t_i))² - (B(t_{i+1}) - B((t_i + t_{i+1}) / 2))²`
cancels the deterministic half-step drifts identically and yields exact second moment
`∑ E[Y_i²] (t_{i+1} - t_i)²`. -/
theorem integral_sq_sum_mul_midpoint_sq_sub_sq (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {Y : ℕ → Ω → ℝ}
    (hY : ∀ i < n, Measurable[ℱ (t i)] (Y i)) (hYi : ∀ i < n, MemLp (Y i) 2 P) :
    (∫ ω, (∑ i ∈ range n, Y i ω *
      ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
        (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) =
      ∑ i ∈ range n, (∫ ω, Y i ω ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  -- 1. Interleave `t` with its midpoints and `Y` with `-Y` to form a `2 * n`-step weighted sum.
  set u : ℕ → ℝ≥0 := TauCeti.interleave t fun i ↦ (t i + t (i + 1)) / 2 with hu_def
  have hu : MonotoneOn u (Set.Iic (2 * n)) := monotoneOn_interleave_midpoint ht
  let H : ℕ → Ω → ℝ := TauCeti.interleave Y fun i ↦ -Y i
  -- 2. Verify adaptedness and `L²` integrability of the interleaved weights `H`.
  have hHm : ∀ j < 2 * n, Measurable[ℱ (u j)] (H j) :=
    (TauCeti.forall_lt_two_mul_interleave_iff
      (P := fun j f ↦ Measurable[ℱ (u j)] f)).2 fun i hi ↦ by
        rw [hu_def, TauCeti.interleave_two_mul, TauCeti.interleave_two_mul_add_one]
        have hle : t i ≤ (t i + t (i + 1)) / 2 :=
          TauCeti.left_le_add_div_two.2 (ht hi.le hi (Nat.le_succ _))
        exact ⟨hY i hi, (hY i hi).neg.mono (ℱ.mono hle) le_rfl⟩
  have hHi : ∀ j < 2 * n, MemLp (H j) 2 P :=
    (TauCeti.forall_lt_two_mul_interleave_iff (P := fun _ f ↦ MemLp f 2 P)).2 fun i hi ↦
      ⟨hYi i hi, (hYi i hi).neg⟩
  -- 3. Apply the centered weighted quadratic-variation `L²` identity on `u` and pair terms.
  have hid := hB.integral_sq_sum_mul_sq_sub_sub hu hHm hHi
  have hlhs (ω : Ω) :
      ∑ j ∈ range (2 * n), H j ω *
        ((B (u (j + 1)) ω - B (u j) ω) ^ 2 - ((u (j + 1) : ℝ) - u j)) =
      ∑ i ∈ range n, Y i ω *
        ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
          (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2) := by
    rw [TauCeti.sum_range_two_mul_interleave t _
      (fun j x y ↦ H j ω * ((B y ω - B x ω) ^ 2 - ((y : ℝ) - x)))]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [H, TauCeti.interleave_two_mul, TauCeti.interleave_two_mul_add_one, Pi.neg_apply]
    push_cast
    ring
  have hrhs :
      2 * ∑ j ∈ range (2 * n), (∫ ω, H j ω ^ 2 ∂P) * ((u (j + 1) : ℝ) - u j) ^ 2 =
        ∑ i ∈ range n, (∫ ω, Y i ω ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
    rw [TauCeti.sum_range_two_mul_interleave t _
      (fun j x y ↦ (∫ ω, H j ω ^ 2 ∂P) * ((y : ℝ) - x) ^ 2), mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [H, TauCeti.interleave_two_mul, TauCeti.interleave_two_mul_add_one, Pi.neg_apply,
      neg_sq]
    push_cast
    ring
  simp_rw [hlhs] at hid
  exact hid.trans hrhs

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For Borel-measurable functions `g i` with square-integrable left evaluations `g i (B (t i))`,
the alternating half-step Brownian quadratic sum has exact second moment
`∑ E[g_i(B_{t_i})²] (t_{i+1} - t_i)²`. Only the finite-dimensional pre-Brownian laws are needed. -/
theorem integral_sq_sum_comp_mul_midpoint_sq_sub_sq (hB : IsPreBrownianReal B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {g : ℕ → ℝ → ℝ}
    (hg : ∀ i < n, Measurable (g i))
    (hgi : ∀ i < n, MemLp (fun ω ↦ g i (B (t i) ω)) 2 P) :
    (∫ ω, (∑ i ∈ range n, g i (B (t i) ω) *
      ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
        (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) =
      ∑ i ∈ range n, (∫ ω, g i (B (t i) ω) ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  -- 1. Replace `B` by a strongly measurable modification `W` to form the natural filtration.
  let W : ℝ≥0 → Ω → ℝ := fun u ↦ (hB.aemeasurable u).aestronglyMeasurable.mk (B u)
  have hWmeas : ∀ u, StronglyMeasurable (W u) :=
    fun u ↦ (hB.aemeasurable u).aestronglyMeasurable.stronglyMeasurable_mk
  have hBW : ∀ u, B u =ᵐ[P] W u :=
    fun u ↦ (hB.aemeasurable u).aestronglyMeasurable.ae_eq_mk
  have hWf := (hB.congr hBW).isFilteredPreBrownianReal_natural hWmeas
  have hYm : ∀ i < n, Measurable[Filtration.natural W hWmeas (t i)] (fun ω ↦ g i (W (t i) ω)) :=
    fun i hi ↦ (hg i hi).comp (hWf.adapted (t i))
  have hYi : ∀ i < n, MemLp (fun ω ↦ g i (W (t i) ω)) 2 P := fun i hi ↦
    (hgi i hi).ae_eq ((hBW (t i)).fun_comp (g i))
  -- 2. Apply the filtered `L²` identity to `W` and transfer both sides back to `B` a.e.
  have hid := hWf.integral_sq_sum_mul_midpoint_sq_sub_sq ht hYm hYi
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ range n,
      B (t i) ω = W (t i) ω ∧
      B ((t i + t (i + 1)) / 2) ω = W ((t i + t (i + 1)) / 2) ω ∧
      B (t (i + 1)) ω = W (t (i + 1)) ω := by
    rw [eventually_all_finset]
    intro i _
    filter_upwards [hBW (t i), hBW ((t i + t (i + 1)) / 2), hBW (t (i + 1))] with ω h₀ hm h₁
    exact ⟨h₀, hm, h₁⟩
  have hlhs :
      (∫ ω, (∑ i ∈ range n, g i (B (t i) ω) *
        ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
          (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) =
      (∫ ω, (∑ i ∈ range n, g i (W (t i) ω) *
        ((W ((t i + t (i + 1)) / 2) ω - W (t i) ω) ^ 2 -
          (W (t (i + 1)) ω - W ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) := by
    refine integral_congr_ae (hall.mono fun ω hω ↦ ?_)
    dsimp only
    congr 1
    refine sum_congr rfl fun i hi ↦ ?_
    obtain ⟨h₀, hm, h₁⟩ := hω i hi
    rw [h₀, hm, h₁]
  have hrhs :
      ∑ i ∈ range n, (∫ ω, g i (W (t i) ω) ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 =
        ∑ i ∈ range n, (∫ ω, g i (B (t i) ω) ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
    refine sum_congr rfl fun i _ ↦ ?_
    congr 1
    exact integral_congr_ae ((hBW (t i)).symm.mono fun ω hω ↦ by simp [hω])
  exact (hlhs.trans hid).trans hrhs

/-- Uniformly bounded Borel left weights bound the second moment of the alternating half-step
Brownian quadratic sum by `C ^ 2 * (t n - t 0) * δ` whenever every grid step is at most `δ`. -/
theorem integral_sq_sum_comp_mul_midpoint_sq_sub_sq_le (hB : IsPreBrownianReal B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {g : ℕ → ℝ → ℝ} {C δ : ℝ}
    (hg : ∀ i < n, Measurable (g i)) (hbound : ∀ i < n, ∀ y, |g i y| ≤ C)
    (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    (∫ ω, (∑ i ∈ range n, g i (B (t i) ω) *
      ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
        (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) ≤
      C ^ 2 * ((t n : ℝ) - t 0) * δ := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hgi : ∀ i < n, MemLp (fun ω ↦ g i (B (t i) ω)) 2 P := by
    intro i hi
    refine MemLp.of_bound ((hg i hi).aestronglyMeasurable.comp_aemeasurable (hB.aemeasurable (t i)))
      C (ae_of_all _ fun ω ↦ ?_)
    simpa only [Real.norm_eq_abs] using hbound i hi (B (t i) ω)
  rw [hB.integral_sq_sum_comp_mul_midpoint_sq_sub_sq ht hg hgi]
  -- Bound `E[g_i(B_{t_i})²] ≤ C²` and `(t_{i+1} - t_i)² ≤ (t_{i+1} - t_i) * δ`, then telescope.
  have hsum :
      ∑ i ∈ range n, (∫ ω, g i (B (t i) ω) ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 ≤
        ∑ i ∈ range n, C ^ 2 * (((t (i + 1) : ℝ) - t i) * δ) := by
    refine sum_le_sum fun i hi ↦ ?_
    have hi' := mem_range.1 hi
    have hstep0 : 0 ≤ (t (i + 1) : ℝ) - t i :=
      sub_nonneg.2 (NNReal.coe_le_coe.2 (ht hi'.le hi' (Nat.le_succ i)))
    have hint_le : ∫ ω, g i (B (t i) ω) ^ 2 ∂P ≤ C ^ 2 := by
      have hpt : ∀ ω, g i (B (t i) ω) ^ 2 ≤ C ^ 2 := fun ω ↦ by
        have hb := abs_le.1 (hbound i hi' (B (t i) ω))
        nlinarith
      calc
        ∫ ω, g i (B (t i) ω) ^ 2 ∂P ≤ ∫ _, C ^ 2 ∂P :=
          integral_mono (hgi i hi').integrable_sq (integrable_const _) hpt
        _ = C ^ 2 := by simp
    have hsq_le : ((t (i + 1) : ℝ) - t i) ^ 2 ≤ ((t (i + 1) : ℝ) - t i) * δ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (hmesh i hi') hstep0
    exact mul_le_mul hint_le hsq_le (sq_nonneg _) (sq_nonneg _)
  refine hsum.trans_eq ?_
  rw [← mul_sum, ← sum_mul, sum_range_sub (fun i ↦ (t i : ℝ)) n]
  ring

/-- On any interleaved deterministic clock `a_0 ≤ c_0 ≤ a_1 ≤ … ≤ a_n`, the difference between
the intermediate-sample sum `∑ B(c_i)(B(a_{i+1}) - B(a_i))` and the symmetric Stratonovich value
`(B(a_n)² - B(a_0)²) / 2` has exact expectation equal to half the net clock asymmetry
`1 / 2 * ∑ ((c_i - a_i) - (a_{i+1} - c_i))`. -/
theorem integral_sum_comp_midpoint_mul_sub_sub_half_sq (hB : IsPreBrownianReal B P)
    {n : ℕ} {a c : ℕ → ℝ≥0} (hac : ∀ i < n, a i ≤ c i ∧ c i ≤ a (i + 1)) :
    (∫ ω, ((∑ i ∈ range n, B (c i) ω * (B (a (i + 1)) ω - B (a i) ω)) -
        (B (a n) ω ^ 2 - B (a 0) ω ^ 2) / 2) ∂P) =
      1 / 2 * ∑ i ∈ range n, (((c i : ℝ) - a i) - ((a (i + 1) : ℝ) - c i)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  simp_rw [fun ω ↦ TauCeti.sum_mul_sub_sub_half_sq (fun i ↦ B (a i) ω) (fun i ↦ B (c i) ω) n]
  have hint (i : ℕ) : Integrable (fun ω ↦
      (B (c i) ω - B (a i) ω) ^ 2 - (B (a (i + 1)) ω - B (c i) ω) ^ 2) P := by
    simpa only [Pi.sub_def] using
      (hB.integrable_pow_sub (a i) (c i) 2).sub (hB.integrable_pow_sub (c i) (a (i + 1)) 2)
  rw [integral_finsetSum (range n) fun i _ ↦ (hint i).const_mul (1 / 2), mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  obtain ⟨h₁, h₂⟩ := hac i (mem_range.1 hi)
  rw [integral_const_mul,
    integral_sub (hB.integrable_pow_sub (a i) (c i) 2) (hB.integrable_pow_sub (c i) (a (i + 1)) 2),
    hB.integral_sq_sub_of_le h₁, hB.integral_sq_sub_of_le h₂]

/-- On any interleaved deterministic clock `a_0 ≤ c_0 ≤ a_1 ≤ … ≤ a_n`, the variance of the
deviation `(∑ B(c_i)(B(a_{i+1}) - B(a_i))) - (B(a_n)² - B(a_0)²) / 2` equals
`1 / 2 * ∑ ((c_i - a_i)² + (a_{i+1} - c_i)²)`. -/
theorem variance_sum_comp_midpoint_mul_sub_sub_half_sq (hB : IsPreBrownianReal B P)
    {n : ℕ} {a c : ℕ → ℝ≥0} (hac : ∀ i < n, a i ≤ c i ∧ c i ≤ a (i + 1)) :
    Var[fun ω ↦ (∑ i ∈ range n, B (c i) ω * (B (a (i + 1)) ω - B (a i) ω)) -
        (B (a n) ω ^ 2 - B (a 0) ω ^ 2) / 2; P] =
      1 / 2 * ∑ i ∈ range n, (((c i : ℝ) - a i) ^ 2 + ((a (i + 1) : ℝ) - c i) ^ 2) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  -- 1. Interleave `a` and `c` into a `2 * n`-step clock `u` with alternating signs `±1/2`.
  let u : ℕ → ℝ≥0 := TauCeti.interleave a c
  have hu : MonotoneOn u (Set.Iic (2 * n)) := TauCeti.monotoneOn_interleave_Iic hac
  let τ : Fin (2 * n + 1) → ℝ≥0 := fun j ↦ u j
  have hτ : Monotone τ := hu.comp_fin_val_Iic
  let sgn : ℕ → ℝ := TauCeti.interleave (fun _ ↦ (1 : ℝ) / 2) (fun _ ↦ -(1 : ℝ) / 2)
  let ξ : Fin (2 * n) → Ω → ℝ := fun j ω ↦
    sgn j * (B (τ j.succ) ω - B (τ j.castSucc) ω) ^ 2
  -- 2. Rewrite the deviation as the sum of independent squared half-step increments `ξ`.
  have hL (j : Fin (2 * n)) : MemLp (ξ j) 2 P :=
    (hB.memLp_sq_sub (τ j.succ) (τ j.castSucc)).const_mul (sgn j)
  have hind := (hB.hasIndepIncrements (2 * n) τ hτ).comp
    (fun j (x : ℝ) ↦ sgn j * x ^ 2) (by fun_prop)
  have hv := IndepFun.variance_sum (s := univ) (fun j _ ↦ hL j)
    (fun i _ j _ hij ↦ hind.indepFun hij)
  have hfun : (fun ω ↦ (∑ i ∈ range n, B (c i) ω * (B (a (i + 1)) ω - B (a i) ω)) -
        (B (a n) ω ^ 2 - B (a 0) ω ^ 2) / 2) =
      ∑ j : Fin (2 * n), ξ j := by
    ext ω
    rw [Finset.sum_apply]
    simp only [ξ, τ, Fin.val_succ, Fin.val_castSucc]
    rw [Fin.sum_univ_eq_sum_range (fun m ↦ sgn m * (B (u (m + 1)) ω - B (u m) ω) ^ 2) (2 * n),
      TauCeti.sum_range_two_mul_interleave a c (fun m x y ↦ sgn m * (B y ω - B x ω) ^ 2),
      TauCeti.sum_mul_sub_sub_half_sq (fun i ↦ B (a i) ω) (fun i ↦ B (c i) ω) n]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [sgn, TauCeti.interleave_two_mul, TauCeti.interleave_two_mul_add_one]
    ring
  -- 3. Sum variances termwise (`Var[(±1/2)(ΔB)²] = 1/2 * (Δu)²`) and pair even/odd terms.
  rw [hfun, hv]
  have hterm (j : Fin (2 * n)) :
      Var[ξ j; P] = 1 / 2 * ((u ((j : ℕ) + 1) : ℝ) - u j) ^ 2 := by
    have hsq_sgn : sgn j ^ 2 = 1 / 4 := by
      dsimp only [sgn]
      rw [TauCeti.interleave_apply]
      split_ifs <;> norm_num
    have hv_sq : Var[fun ω ↦ (B (τ j.succ) ω - B (τ j.castSucc) ω) ^ 2; P] =
        2 * ((τ j.succ : ℝ) - τ j.castSucc) ^ 2 := by
      rw [variance_eq_sub (hB.memLp_sq_sub (τ j.succ) (τ j.castSucc))]
      simp only [Pi.pow_def, ← pow_mul, Nat.reduceMul]
      rw [hB.integral_sq_sub_of_le (hτ (Fin.castSucc_le_succ j)),
        hB.integral_pow_four_sub_of_le (hτ (Fin.castSucc_le_succ j))]
      ring
    dsimp only [ξ]
    rw [variance_const_mul, hsq_sgn, hv_sq]
    dsimp [τ]
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ 1 / 2 * ((u (m + 1) : ℝ) - u m) ^ 2) (2 * n),
    ← mul_sum, TauCeti.sum_range_two_mul_interleave a c (fun _ x y ↦ ((y : ℝ) - x) ^ 2)]

/-- When every clock step `a (i + 1) - a i` is at most `δ`, the variance of the deviation
`(∑ B(c_i)(B(a_{i+1}) - B(a_i))) - (B(a_n)² - B(a_0)²) / 2` on an interleaved deterministic clock
`a_0 ≤ c_0 ≤ a_1 ≤ … ≤ a_n` is at most `1 / 2 * (a n - a 0) * δ`. -/
theorem variance_sum_comp_midpoint_mul_sub_sub_half_sq_le (hB : IsPreBrownianReal B P)
    {n : ℕ} {a c : ℕ → ℝ≥0} {δ : ℝ} (hac : ∀ i < n, a i ≤ c i ∧ c i ≤ a (i + 1))
    (hmesh : ∀ i < n, (a (i + 1) : ℝ) - a i ≤ δ) :
    Var[fun ω ↦ (∑ i ∈ range n, B (c i) ω * (B (a (i + 1)) ω - B (a i) ω)) -
        (B (a n) ω ^ 2 - B (a 0) ω ^ 2) / 2; P] ≤
      1 / 2 * ((a n : ℝ) - a 0) * δ := by
  rw [hB.variance_sum_comp_midpoint_mul_sub_sub_half_sq hac]
  have hsum : ∑ i ∈ range n, (((c i : ℝ) - a i) ^ 2 + ((a (i + 1) : ℝ) - c i) ^ 2) ≤
      ∑ i ∈ range n, ((a (i + 1) : ℝ) - a i) * δ := by
    refine sum_le_sum fun i hi ↦ ?_
    have hi' := mem_range.1 hi
    obtain ⟨h₁, h₂⟩ := hac i hi'
    have hu0 : 0 ≤ (c i : ℝ) - a i := sub_nonneg.2 (NNReal.coe_le_coe.2 h₁)
    have hv0 : 0 ≤ (a (i + 1) : ℝ) - c i := sub_nonneg.2 (NNReal.coe_le_coe.2 h₂)
    have hsq1 : ((c i : ℝ) - a i) ^ 2 + ((a (i + 1) : ℝ) - c i) ^ 2 ≤
        ((a (i + 1) : ℝ) - a i) ^ 2 := by nlinarith
    have hsq2 : ((a (i + 1) : ℝ) - a i) ^ 2 ≤ ((a (i + 1) : ℝ) - a i) * δ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (hmesh i hi') (by linarith)
    exact hsq1.trans hsq2
  have htel : ∑ i ∈ range n, ((a (i + 1) : ℝ) - a i) * δ = ((a n : ℝ) - a 0) * δ := by
    rw [← sum_mul, sum_range_sub (fun i ↦ (a i : ℝ)) n]
  linarith

/-- **Biased-clock temporal-midpoint limit.** Along deterministic clock partitions
`A₀ = a n 0 ≤ c n 0 ≤ a n 1 ≤ … ≤ a n (k n) = A₁` whose clock mesh `(a n (i + 1) - a n i)` tends
to zero and whose net half-step clock asymmetry
`1 / 2 * ∑ ((c n i - a n i) - (a n (i + 1) - c n i))` converges to `β`, the intermediate-sample
sums `∑ B(c n i)(B(a n (i + 1)) - B(a n i))` converge in probability to
`(B(A₁)² - B(A₀)²) / 2 + β`. In particular, for a clock splitting every dyadic interval in ratio
`p : (1 - p)` with `p ≠ 1 / 2` and `A₀ < A₁`, the limit shifts from the symmetric Stratonovich
value `(B(A₁)² - B(A₀)²) / 2` by `(p - 1 / 2) * (A₁ - A₀) ≠ 0`. -/
theorem tendstoInMeasure_sum_comp_midpoint_mul_sub (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {A₀ A₁ : ℝ≥0} {k : ι → ℕ} {a c : ι → ℕ → ℝ≥0}
    (ha₀ : ∀ n, a n 0 = A₀) (ha₁ : ∀ n, a n (k n) = A₁)
    (hac : ∀ n, ∀ i < k n, a n i ≤ c n i ∧ c n i ≤ a n (i + 1))
    {δ : ι → ℝ} (hmesh : ∀ n, ∀ i < k n, (a n (i + 1) : ℝ) - a n i ≤ δ n)
    (hδ : Tendsto δ l (𝓝 0))
    {β : ℝ}
    (hβ : Tendsto (fun n ↦ 1 / 2 * ∑ i ∈ range (k n),
      (((c n i : ℝ) - a n i) - ((a n (i + 1) : ℝ) - c n i))) l (𝓝 β)) :
    TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ range (k n), B (c n i) ω * (B (a n (i + 1)) ω - B (a n i) ω))
      l (fun ω ↦ (B A₁ ω ^ 2 - B A₀ ω ^ 2) / 2 + β) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let D : ι → Ω → ℝ := fun n ω ↦
    (∑ i ∈ range (k n), B (c n i) ω * (B (a n (i + 1)) ω - B (a n i) ω)) -
      (B (a n (k n)) ω ^ 2 - B (a n 0) ω ^ 2) / 2
  let μ : ι → ℝ := fun n ↦
    1 / 2 * ∑ i ∈ range (k n), (((c n i : ℝ) - a n i) - ((a n (i + 1) : ℝ) - c n i))
  -- 1. Check `D n ∈ L²` via `TauCeti.sum_mul_sub_sub_half_sq`.
  have hD_lp (n : ι) : MemLp (D n) 2 P := by
    have hid : D n = fun ω ↦ ∑ i ∈ range (k n),
        1 / 2 * ((B (c n i) ω - B (a n i) ω) ^ 2 -
          (B (a n (i + 1)) ω - B (c n i) ω) ^ 2) :=
      funext fun ω ↦ TauCeti.sum_mul_sub_sub_half_sq (fun i ↦ B (a n i) ω)
        (fun i ↦ B (c n i) ω) (k n)
    rw [hid]
    exact memLp_finsetSum (range (k n)) fun i _ ↦
      ((hB.memLp_sq_sub (c n i) (a n i)).sub
        (hB.memLp_sq_sub (a n (i + 1)) (c n i))).const_mul (1 / 2)
  -- 2. Bound the variance `E[(D n - μ n)²]` by `1 / 2 * (A₁ - A₀) * δ n`.
  have hvar_le (n : ι) :
      ∫ ω, (D n ω - μ n) ^ 2 ∂P ≤ 1 / 2 * ((A₁ : ℝ) - A₀) * δ n := by
    have hmean : ∫ ω, D n ω ∂P = μ n :=
      hB.integral_sum_comp_midpoint_mul_sub_sub_half_sq (hac n)
    rw [← hmean, ← variance_eq_integral (hD_lp n).aemeasurable]
    simpa only [D, ha₁ n, ha₀ n] using
      hB.variance_sum_comp_midpoint_mul_sub_sub_half_sq_le (hac n) (hmesh n)
  -- 3. Combine `D n - μ n → 0` (in `L²`, hence in measure) with `μ n → β` to get `D n → β`.
  have hD_sub : TendstoInMeasure P (fun n ω ↦ D n ω - μ n) l (fun _ ↦ 0) := by
    refine tendstoInMeasure_of_tendsto_integral_norm_sq
      (Eventually.of_forall fun n ↦ by
        simpa only [sub_zero, Pi.sub_apply] using
          ((hD_lp n).sub (memLp_const (μ n))).norm.integrable_sq) ?_
    simp only [sub_zero, Real.norm_eq_abs, sq_abs]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using hδ.const_mul (1 / 2 * ((A₁ : ℝ) - A₀)))
      (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) hvar_le
  have hD_lim : TendstoInMeasure P D l (fun _ ↦ β) :=
    ((hD_sub.add (hβ.tendstoInMeasure_const (μ := P))).congr_right
      (ae_of_all _ fun _ ↦ zero_add β)).congr_left
      fun n ↦ ae_of_all _ fun ω ↦ sub_add_cancel (D n ω) (μ n)
  exact ((MeasureTheory.tendstoInMeasure_const (μ := P) (l := l)
      (fun ω ↦ (B A₁ ω ^ 2 - B A₀ ω ^ 2) / 2)).add hD_lim).congr_left
    fun n ↦ ae_of_all _ fun ω ↦ by
      dsimp only [D]
      rw [ha₁ n, ha₀ n]
      ring

end ProbabilityTheory.IsPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem tendstoInMeasure_sq_sum_range (hB : IsPreBrownianReal B P)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ range (k n), (B (π n (i + 1)) ω - B (π n i) ω) ^ 2)
      atTop (fun _ ↦ (b : ℝ) - a) :=
  (hB.tendstoInMeasure_quadraticSum (fun n ↦ (hmono n).comp_fin_val_Iic)
    (fun n ↦ ha n) (fun n ↦ hb n)
    (fun n (i : Fin (k n)) ↦ hmesh n i i.isLt) hδ).congr_left
    fun n ↦ ae_of_all _ fun ω ↦ quadraticSum_comp_fin_val B (π n) ω

/-- The midpoint-refined quadratic sums `∑ ((B m_i - B t_i)² + (B t_{i+1} - B m_i)²)` converge in
probability to `b - a`. -/
private theorem tendstoInMeasure_refined_sq_sum (hB : IsPreBrownianReal B P)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
      ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 +
        (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2))
      atTop (fun _ ↦ (b : ℝ) - a) :=
  (tendstoInMeasure_sq_sum_range hB (a := a) (b := b)
    (fun n ↦ monotoneOn_interleave_midpoint (hmono n))
    (fun n ↦ by simp [ha n])
    (fun n ↦ by simp [hb n])
    (fun n _ hj ↦ interleave_midpoint_step_le (hmono n) (hmesh n) hj) hδ).congr_left
    fun n ↦ ae_of_all _ fun ω ↦
      TauCeti.sum_range_two_mul_interleave (π n) _ (fun _ x y ↦ (B y ω - B x ω) ^ 2) (k n)

/-- For a Borel-measurable function `g` with `|g y| ≤ C`, the alternating half-step Brownian
quadratic sums converge to zero in probability along vanishing-mesh partitions of `[a, b]`. -/
private theorem tendstoInMeasure_sum_mul_midpoint_sq_sub_sq_of_le (hB : IsPreBrownianReal B P)
    {g : ℝ → ℝ} {C : ℝ} (hg : Measurable g) (hbound : ∀ y, |g y| ≤ C)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n), g (B (π n i) ω) *
      ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
        (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2))
      atTop (fun _ ↦ 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply tendstoInMeasure_of_tendsto_integral_norm_sq
  · refine Eventually.of_forall fun n ↦ ?_
    have hlp : MemLp (fun ω ↦ ∑ i ∈ range (k n), g (B (π n i) ω) *
        ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
          (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2)) 2 P := by
      refine memLp_finsetSum (range (k n)) fun i _ ↦ ?_
      have hd : MemLp (fun ω ↦
          (B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
            (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2) 2 P :=
        (hB.memLp_sq_sub _ _).sub (hB.memLp_sq_sub _ _)
      have hgm : AEStronglyMeasurable (fun ω ↦ g (B (π n i) ω)) P :=
        hg.aestronglyMeasurable.comp_aemeasurable (hB.aemeasurable (π n i))
      exact hd.of_le_mul (c := C) (hgm.mul hd.aestronglyMeasurable) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hbound _) (abs_nonneg _))
    simpa only [sub_zero] using hlp.norm.integrable_sq
  · simp only [sub_zero, Real.norm_eq_abs, sq_abs]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using hδ.const_mul (C ^ 2 * ((b : ℝ) - a)))
      (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) fun n ↦ ?_
    simpa only [hb n, ha n] using
      hB.integral_sq_sum_comp_mul_midpoint_sq_sub_sq_le (hmono n)
        (fun _ _ ↦ hg) (fun _ _ y ↦ hbound y) (hmesh n)

/-- Because Brownian sample paths are almost surely continuous on `[a, b]`, the grid-exceedance
events `⋃ (n : ℕ) (i : Fin (k n)), {ω | M < |g (B (π n i) ω)|}` have infimum measure zero for any
continuous `g`. -/
private theorem iInf_measure_iUnion_lt_abs_eq_zero (hB : IsBrownianReal B P)
    {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b) :
    (⨅ M : ℕ, P (⋃ (n : ℕ) (i : Fin (k n)), {ω | (M : ℝ) < |g (B (π n i) ω)|})) = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let F (M : ℕ) : Set Ω := ⋃ (n : ℕ) (i : Fin (k n)), {ω | (M : ℝ) < |g (B (π n i) ω)|}
  have hF_meas (M : ℕ) : NullMeasurableSet (F M) P :=
    NullMeasurableSet.iUnion fun n ↦ NullMeasurableSet.iUnion fun i ↦
      ((continuous_abs.comp hg).measurable.comp_aemeasurable
        (hB.aemeasurable (π n i))).nullMeasurableSet_preimage measurableSet_Ioi
  have hF_anti : Antitone F := by
    intro M₁ M₂ hle ω hω
    simp only [F, mem_iUnion, mem_ofPred_eq] at hω ⊢
    obtain ⟨n, i, hi⟩ := hω
    exact ⟨n, i, (Nat.cast_le.2 hle).trans_lt hi⟩
  have hF_inter : (⋂ M : ℕ, F M) ⊆ {ω | ¬Continuous (B · ω)} := by
    intro ω hω hc
    obtain ⟨C, hC⟩ :=
      (isCompact_Icc (a := a) (b := b) |>.image ((continuous_abs.comp hg).comp hc)).bddAbove
    obtain ⟨M, hMC⟩ := exists_nat_ge C
    have hM := mem_iInter.1 hω M
    simp only [F, mem_iUnion, mem_ofPred_eq] at hM
    obtain ⟨n, i, hgt⟩ := hM
    have hmem_i : π n i ∈ Icc a b := grid_mem_Icc (hmono n) (ha n) (hb n) i.isLt.le
    exact hgt.not_ge ((hC ⟨π n i, hmem_i, rfl⟩).trans hMC)
  change (⨅ M : ℕ, P (F M)) = 0
  rw [← hF_anti.measure_iInter hF_meas ⟨0, measure_ne_top P _⟩]
  exact measure_mono_null hF_inter (ae_iff.1 hB.cont)

/-- For any continuous function `g`, the alternating half-step Brownian quadratic sums
`∑ g(B_{t_i}) ((B_{(t_i + t_{i+1}) / 2} - B_{t_i})² - (B_{t_{i+1}} - B_{(t_i + t_{i+1}) / 2})²)`
converge to zero in probability along vanishing-mesh deterministic partitions of `[a, b]`, with no
growth or moment bound on `g`. -/
theorem tendstoInMeasure_sum_mul_midpoint_sq_sub_sq (hB : IsBrownianReal B P)
    {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n), g (B (π n i) ω) *
      ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
        (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2))
      atTop (fun _ ↦ 0) := by
  let trunc (M : ℕ) (y : ℝ) : ℝ := max (-(M : ℝ)) (min (M : ℝ) (g y))
  have htrunc_meas (M : ℕ) : Measurable (trunc M) :=
    (continuous_const.max (continuous_const.min hg)).measurable
  have htrunc_le (M : ℕ) (y : ℝ) : |trunc M y| ≤ M :=
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) M]) (min_le_left _ _)⟩
  have htrunc_eq (M : ℕ) {y : ℝ} (hy : |g y| ≤ M) : trunc M y = g y := by
    obtain ⟨h₁, h₂⟩ := abs_le.1 hy
    simp only [trunc, min_eq_right h₂, max_eq_right h₁]
  refine TauCeti.tendstoInMeasure_of_iInf_measure_eq_zero
    (iInf_measure_iUnion_lt_abs_eq_zero hB hg hmono ha hb)
    (fun M ↦ tendstoInMeasure_sum_mul_midpoint_sq_sub_sq_of_le hB.toIsPreBrownianReal
      (htrunc_meas M) (htrunc_le M) hmono ha hb hmesh hδ)
    fun M ↦ Eventually.of_forall fun n ↦ ae_of_all _ fun ω hω ↦ ?_
  have heq : (∑ i ∈ range (k n), trunc M (B (π n i) ω) *
      ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
        (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2)) =
      ∑ i ∈ range (k n), g (B (π n i) ω) *
        ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
          (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2) := by
    refine sum_congr rfl fun i hi ↦ ?_
    have hle : |g (B (π n i) ω)| ≤ M := by
      by_contra hlt
      exact hω (mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨⟨i, mem_range.1 hi⟩, not_le.1 hlt⟩⟩)
    rw [htrunc_eq M hle]
  rw [heq]

/-- For a `C¹` function `h`, the cross-increment sums
`∑ (h(B_{t_{i+1}}) - h(B_{t_i}))(B_{t_{i+1}} - B_{t_i})` differ from the left-weighted Brownian
quadratic sums `∑ h'(B_{t_i})(B_{t_{i+1}} - B_{t_i})²` by an error tending to zero in probability
along vanishing-mesh partitions of `[a, b]`. -/
theorem tendstoInMeasure_sum_sub_mul_sub_sub_deriv_mul_sq (hB : IsBrownianReal B P)
    {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦
      (∑ i ∈ range (k n),
        (h (B (π n (i + 1)) ω) - h (B (π n i) ω)) * (B (π n (i + 1)) ω - B (π n i) ω)) -
      ∑ i ∈ range (k n),
        deriv h (B (π n i) ω) * (B (π n (i + 1)) ω - B (π n i) ω) ^ 2)
      atTop (fun _ ↦ 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact TauCeti.Probability.tendstoInMeasure_sum_sub_mul_sub_sub_deriv_mul_sq
    (s := Icc a b) isCompact_Icc hh
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi)
    (fun n i hi ↦ grid_dist_le (hmono n) hi (hmesh n i hi))
    hδ
    (fun n i _ ↦ (hB.aemeasurable (π n i)).aestronglyMeasurable)
    (hB.cont.mono fun _ hc ↦ hc.continuousOn)
    (tendstoInMeasure_sq_sum_range hB.toIsPreBrownianReal hmono ha hb hmesh hδ)

/-- **Brownian symmetric-endpoint Stratonovich convergence.** For a `C¹` function `h` with
primitive `H`, along deterministic partitions `a = π n 0 ≤ … ≤ π n (k n) = b` whose mesh tends to
zero, the symmetric-endpoint sums
`∑ (h(B_{t_i}) + h(B_{t_{i+1}})) / 2 * (B_{t_{i+1}} - B_{t_i})` converge in probability to
`H(B_b) - H(B_a)`. -/
theorem tendstoInMeasure_sum_half_add_mul_sub (hB : IsBrownianReal B P)
    {h H : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hH : ∀ y, HasDerivAt H (h y) y)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
        (h (B (π n i) ω) + h (B (π n (i + 1)) ω)) / 2 * (B (π n (i + 1)) ω - B (π n i) ω))
      atTop (fun ω ↦ H (B b ω) - H (B a ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact TauCeti.Probability.tendstoInMeasure_sum_half_add_mul_sub
    (s := Icc a b) isCompact_Icc hh hH ha hb
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi)
    (fun n i hi ↦ grid_dist_le (hmono n) hi (hmesh n i hi))
    hδ
    (fun n i _ ↦ (hB.aemeasurable (π n i)).aestronglyMeasurable)
    (hB.cont.mono fun _ hc ↦ hc.continuousOn)
    (tendstoInMeasure_sq_sum_range hB.toIsPreBrownianReal hmono ha hb hmesh hδ)

/-- Perturbing Brownian motion by an almost surely continuous bounded-variation process `A` on
`[a, b]` preserves the symmetric-endpoint Stratonovich chain rule: the symmetric-endpoint sums of
`B + A` converge in probability to `H((B + A)_b) - H((B + A)_a)`, with no integrability or
adaptedness assumption on `A`. -/
theorem tendstoInMeasure_sum_half_add_mul_sub_add_of_boundedVariationOn
    (hB : IsBrownianReal B P) {A : ℝ≥0 → Ω → ℝ}
    {h H : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hH : ∀ y, HasDerivAt H (h y) y)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hAmeas : ∀ n, ∀ i ≤ k n, AEStronglyMeasurable (A (π n i)) P)
    (hA : ∀ᵐ ω ∂P, ContinuousOn (A · ω) (Icc a b) ∧ BoundedVariationOn (A · ω) (Icc a b)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
        (h ((B + A) (π n i) ω) + h ((B + A) (π n (i + 1)) ω)) / 2 *
          ((B + A) (π n (i + 1)) ω - (B + A) (π n i) ω))
      atTop (fun ω ↦ H ((B + A) b ω) - H ((B + A) a ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hqv := (hB.tendstoInMeasure_quadraticSum_add_of_boundedVariationOn
    (fun n ↦ (hmono n).comp_fin_val_Iic)
    (fun n ↦ ha n) (fun n ↦ hb n)
    (fun n i ↦ grid_dist_le (hmono n) i.isLt (hmesh n i i.isLt))
    hδ (fun n j ↦ hAmeas n j (Nat.le_of_lt_succ j.isLt)) hA).congr_left
    fun n ↦ ae_of_all _ fun ω ↦ quadraticSum_comp_fin_val (B + A) (π n) ω
  exact TauCeti.Probability.tendstoInMeasure_sum_half_add_mul_sub
    (s := Icc a b) isCompact_Icc hh hH ha hb
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi)
    (fun n i hi ↦ grid_dist_le (hmono n) hi (hmesh n i hi))
    hδ
    (fun n i hi ↦ ((hB.aemeasurable (π n i)).aestronglyMeasurable).add (hAmeas n i hi))
    (by
      filter_upwards [hB.cont, hA] with ω hcB hcA
      exact hcB.continuousOn.add hcA.1)
    hqv

/-- **Brownian temporal-midpoint Stratonovich convergence.** For a `C¹` function `h` with primitive
`H`, along deterministic partitions `a = π n 0 ≤ … ≤ π n (k n) = b` whose mesh tends to zero, the
temporal-midpoint sums `∑ h(B_{(t_i + t_{i+1}) / 2}) * (B_{t_{i+1}} - B_{t_i})` converge in
probability to `H(B_b) - H(B_a)`. -/
theorem tendstoInMeasure_sum_midpoint_mul_sub (hB : IsBrownianReal B P)
    {h H : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hH : ∀ y, HasDerivAt H (h y) y)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
        h (B ((π n i + π n (i + 1)) / 2) ω) * (B (π n (i + 1)) ω - B (π n i) ω))
      atTop (fun ω ↦ H (B b ω) - H (B a ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  -- Decompose each midpoint sum into three pieces:
  --   midpoint = (midpoint - symmetric - alternating) + alternating + symmetric.
  -- 1. Remainder `(midpoint - symmetric - alternating) → 0` via the deterministic `C¹` reduction.
  let u (n : ℕ) : ℕ → ℝ≥0 := TauCeti.interleave (π n) fun i ↦ (π n i + π n (i + 1)) / 2
  have hu_mono (n : ℕ) : MonotoneOn (u n) (Set.Iic (2 * k n)) :=
    monotoneOn_interleave_midpoint (hmono n)
  have hu_dist (n : ℕ) : ∀ i < k n,
      dist ((π n i + π n (i + 1)) / 2) (π n i) ≤ δ n ∧
      dist (π n (i + 1)) ((π n i + π n (i + 1)) / 2) ≤ δ n :=
    (TauCeti.forall_lt_two_mul_interleave_succ_iff (R := fun _ x y ↦ dist y x ≤ δ n)).1
      fun _ hj ↦ grid_dist_le (hu_mono n) hj (interleave_midpoint_step_le (hmono n) (hmesh n) hj)
  have hmem_mid (n i : ℕ) (hi : i < k n) : (π n i + π n (i + 1)) / 2 ∈ Icc a b := by
    have hidx : 2 * i + 1 ≤ 2 * k n := by omega
    simpa only [u, TauCeti.interleave_two_mul_add_one] using
      grid_mem_Icc (hu_mono n) (by simp [u, ha n]) (by simp [u, hb n]) hidx
  have hR₁ := TauCeti.Probability.tendstoInMeasure_sum_midpoint_sub_half_add_sub_half_deriv
    (s := Icc a b) isCompact_Icc hh
    (x := π) (z := fun n i ↦ (π n i + π n (i + 1)) / 2) (y := fun n i ↦ π n (i + 1))
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi.le)
    hmem_mid
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi)
    (fun n i hi ↦ (hu_dist n i hi).1)
    (fun n i hi ↦ (hu_dist n i hi).2)
    hδ
    (fun n i _ ↦ (hB.aemeasurable _).aestronglyMeasurable)
    (fun n i _ ↦ (hB.aemeasurable _).aestronglyMeasurable)
    (fun n i _ ↦ (hB.aemeasurable _).aestronglyMeasurable)
    (hB.cont.mono fun _ hc ↦ hc.continuousOn)
    (tendstoInMeasure_refined_sq_sum hB.toIsPreBrownianReal hmono ha hb hmesh hδ)
  -- 2. Alternating half-step quadratic term `1/2 * ∑ h'(B_{t_i}) ((Δ₁B)² - (Δ₂B)²) → 0`.
  have hR₂ : TendstoInMeasure P
      (fun n ω ↦ 1 / 2 * ∑ i ∈ range (k n), deriv h (B (π n i) ω) *
        ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
          (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2))
      atTop (fun _ ↦ 0) := by
    simpa only [smul_eq_mul, mul_zero] using
      (hB.tendstoInMeasure_sum_mul_midpoint_sq_sub_sq hh.continuous_deriv_one
        hmono ha hb hmesh hδ).const_smul ((1 : ℝ) / 2)
  -- 3. Symmetric-endpoint sum `→ H(B_b) - H(B_a)`.
  have hsym := hB.tendstoInMeasure_sum_half_add_mul_sub hh hH hmono ha hb hmesh hδ
  -- 4. Reassemble `remainder + alternating + symmetric = midpoint`.
  refine (((hR₁.add hR₂).add hsym).congr_right
    (ae_of_all _ fun ω ↦ by simp only [zero_add])).congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ ↦ by ring

end ProbabilityTheory.IsBrownianReal
