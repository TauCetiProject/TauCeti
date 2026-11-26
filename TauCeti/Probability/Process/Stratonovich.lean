/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.Calculus.Taylor.Symmetric
import TauCeti.Probability.Process.SubsequenceLimit

/-!
# Symmetric-endpoint, midpoint, and cross-increment limits for continuous processes

When the unweighted quadratic sums of a continuous real-valued process converge in probability
along finite partitions of a compact set with vanishing mesh, deterministic `C¹` oscillation
estimates upgrade pathwise along almost-everywhere convergent subsequences without requiring
adaptedness, martingale structure, or moment bounds on the transformed process:

* **Cross-increment reduction** (`tendstoInMeasure_sum_sub_mul_sub_sub_deriv_mul_sq`): for `C¹`
  `h`, the cross-increment sum `∑ (h(X_{t_{i+1}}) - h(X_{t_i}))(X_{t_{i+1}} - X_{t_i})` differs
  from the left-weighted quadratic sum `∑ h'(X_{t_i})(X_{t_{i+1}} - X_{t_i})²` by an error tending
  to zero in probability.
* **Symmetric-endpoint chain rule** (`tendstoInMeasure_sum_half_add_mul_sub`): if `H` has
  derivative `h` and `h` is `C¹`, the symmetric-endpoint Stratonovich sums
  `∑ (h(X_{t_i}) + h(X_{t_{i+1}})) / 2 * (X_{t_{i+1}} - X_{t_i})` over partitions from `a` to `b`
  converge in probability to `H(X_b) - H(X_a)`. Because only convergence in probability of the
  unweighted quadratic sums and sample-path continuity are used, the result applies unchanged to
  continuous semimartingale perturbations whose quadratic-sum limit exists in probability.
* **Midpoint-to-symmetric reduction**
  (`tendstoInMeasure_sum_midpoint_sub_half_add_sub_half_deriv`): along triples `(x, z, y)` with
  vanishing half-step distances and convergent refined quadratic sums, replacing the symmetric
  endpoint average by an intermediate sample `h(X_z)` isolates the alternating half-step quadratic
  term `1 / 2 * ∑ h'(X_x) * ((X_z - X_x)² - (X_y - X_z)²)`. Unlike the symmetric-endpoint rule,
  whether this alternating quadratic term vanishes depends on the fine-scale law of the process
  rather than its total quadratic variation alone.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter V, §5.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open Finset Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.Probability

variable {Ω T : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [PseudoMetricSpace T]

/-- When unweighted quadratic sums converge in probability on a compact set, the `C¹`
cross-increment sum `∑ (h(X_{t_{i+1}}) - h(X_{t_i}))(X_{t_{i+1}} - X_{t_i})` differs from the
left-weighted quadratic sum `∑ h'(X_{t_i})(X_{t_{i+1}} - X_{t_i})²` by an error tending to zero in
probability. Only grid-date measurability and almost-sure continuity on `s` are required. -/
theorem tendstoInMeasure_sum_sub_mul_sub_sub_deriv_mul_sq [IsFiniteMeasure P]
    {X : T → Ω → ℝ} {s : Set T} (hs : IsCompact s)
    {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {k : ℕ → ℕ} {π : ℕ → ℕ → T} (hmem : ∀ n, ∀ i ≤ k n, π n i ∈ s)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, dist (π n (i + 1)) (π n i) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hXmeas : ∀ n, ∀ i ≤ k n, AEStronglyMeasurable (X (π n i)) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s)
    {V : Ω → ℝ}
    (hV : TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ range (k n), (X (π n (i + 1)) ω - X (π n i) ω) ^ 2) atTop V) :
    TendstoInMeasure P (fun n ω ↦
      (∑ i ∈ range (k n),
        (h (X (π n (i + 1)) ω) - h (X (π n i) ω)) * (X (π n (i + 1)) ω - X (π n i) ω)) -
      ∑ i ∈ range (k n),
        deriv h (X (π n i) ω) * (X (π n (i + 1)) ω - X (π n i) ω) ^ 2)
      atTop (fun _ ↦ 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun ω ↦
      (∑ i ∈ range (k n),
        (h (X (π n (i + 1)) ω) - h (X (π n i) ω)) * (X (π n (i + 1)) ω - X (π n i) ω)) -
      ∑ i ∈ range (k n),
        deriv h (X (π n i) ω) * (X (π n (i + 1)) ω - X (π n i) ω) ^ 2) P := by
    have : Continuous h := hh.continuous
    have : Continuous (deriv h) := hh.continuous_deriv_one
    refine AEStronglyMeasurable.sub
      (Finset.aestronglyMeasurable_fun_sum _ fun i hi ↦ ?_)
      (Finset.aestronglyMeasurable_fun_sum _ fun i hi ↦ ?_)
    · have := hXmeas n i (mem_range.1 hi).le
      have := hXmeas n (i + 1) (mem_range.1 hi)
      fun_prop
    · have := hXmeas n i (mem_range.1 hi).le
      have := hXmeas n (i + 1) (mem_range.1 hi)
      fun_prop
  refine tendstoInMeasure_of_tendsto_of_continuousOn_range hs hmem hmesh hδ hc hV hm ?_
  intro ω idx L R d hLR hd_le hd hQ
  exact TauCeti.tendsto_sum_sub_mul_sub_sub_deriv_mul_sq
    (x := fun j i ↦ X (π (idx j) i) ω) (n := fun j ↦ k (idx j)) (δ := d)
    (fun z _ ↦ (hh.differentiable_one z).hasDerivAt.hasDerivWithinAt)
    hh.continuous_deriv_one.continuousOn
    (Eventually.of_forall fun j i hi ↦ hLR _ (hmem (idx j) i hi))
    (Eventually.of_forall hd_le)
    hd hQ.isBoundedUnder_le

/-- When `H` has derivative `h` and `h` is `C¹`, the difference between the symmetric-endpoint sum
`∑ (h(X_{t_i}) + h(X_{t_{i+1}})) / 2 * (X_{t_{i+1}} - X_{t_i})` and `H(X_{t_{k n}}) - H(X_{t_0})`
tends to zero in probability whenever the unweighted quadratic sums converge in probability and
the sample paths are almost surely continuous on `s`. -/
theorem tendstoInMeasure_sum_half_add_mul_sub_sub [IsFiniteMeasure P]
    {X : T → Ω → ℝ} {s : Set T} (hs : IsCompact s)
    {h H : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hH : ∀ y, HasDerivAt H (h y) y)
    {k : ℕ → ℕ} {π : ℕ → ℕ → T} (hmem : ∀ n, ∀ i ≤ k n, π n i ∈ s)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, dist (π n (i + 1)) (π n i) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hXmeas : ∀ n, ∀ i ≤ k n, AEStronglyMeasurable (X (π n i)) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s)
    {V : Ω → ℝ}
    (hV : TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ range (k n), (X (π n (i + 1)) ω - X (π n i) ω) ^ 2) atTop V) :
    TendstoInMeasure P (fun n ω ↦
      (∑ i ∈ range (k n),
        (h (X (π n i) ω) + h (X (π n (i + 1)) ω)) / 2 * (X (π n (i + 1)) ω - X (π n i) ω)) -
      (H (X (π n (k n)) ω) - H (X (π n 0) ω)))
      atTop (fun _ ↦ 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun ω ↦
      (∑ i ∈ range (k n),
        (h (X (π n i) ω) + h (X (π n (i + 1)) ω)) / 2 * (X (π n (i + 1)) ω - X (π n i) ω)) -
      (H (X (π n (k n)) ω) - H (X (π n 0) ω))) P := by
    have : Continuous h := hh.continuous
    have : Continuous H := continuous_iff_continuousAt.2 fun y ↦ (hH y).continuousAt
    have := hXmeas n (k n) le_rfl
    have := hXmeas n 0 (Nat.zero_le _)
    refine AEStronglyMeasurable.sub
      (Finset.aestronglyMeasurable_fun_sum _ fun i hi ↦ ?_) (by fun_prop)
    have := hXmeas n i (mem_range.1 hi).le
    have := hXmeas n (i + 1) (mem_range.1 hi)
    fun_prop
  refine tendstoInMeasure_of_tendsto_of_continuousOn_range hs hmem hmesh hδ hc hV hm ?_
  intro ω idx L R d hLR hd_le hd hQ
  exact TauCeti.tendsto_sum_half_add_mul_sub_sub
    (x := fun j i ↦ X (π (idx j) i) ω) (n := fun j ↦ k (idx j)) (δ := d)
    (fun z _ ↦ (hH z).hasDerivWithinAt)
    (fun z _ ↦ (hh.differentiable_one z).hasDerivAt.hasDerivWithinAt)
    hh.continuous_deriv_one.continuousOn
    (Eventually.of_forall fun j i hi ↦ hLR _ (hmem (idx j) i hi))
    (Eventually.of_forall hd_le)
    hd hQ.isBoundedUnder_le

/-- **Symmetric-endpoint Stratonovich chain rule for continuous processes.** Along partitions of a
compact set with fixed endpoints `a` and `b`, vanishing mesh, and unweighted quadratic sums
converging in probability, the symmetric-endpoint sums for a `C¹` integrand `h` with primitive `H`
converge in probability to `H(X_b) - H(X_a)`. -/
theorem tendstoInMeasure_sum_half_add_mul_sub [IsFiniteMeasure P]
    {X : T → Ω → ℝ} {s : Set T} (hs : IsCompact s)
    {h H : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hH : ∀ y, HasDerivAt H (h y) y)
    {a b : T} {k : ℕ → ℕ} {π : ℕ → ℕ → T}
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    (hmem : ∀ n, ∀ i ≤ k n, π n i ∈ s)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, dist (π n (i + 1)) (π n i) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hXmeas : ∀ n, ∀ i ≤ k n, AEStronglyMeasurable (X (π n i)) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s)
    {V : Ω → ℝ}
    (hV : TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ range (k n), (X (π n (i + 1)) ω - X (π n i) ω) ^ 2) atTop V) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
        (h (X (π n i) ω) + h (X (π n (i + 1)) ω)) / 2 * (X (π n (i + 1)) ω - X (π n i) ω))
      atTop (fun ω ↦ H (X b ω) - H (X a ω)) := by
  have hdiff := tendstoInMeasure_sum_half_add_mul_sub_sub hs hh hH hmem hmesh hδ hXmeas hc hV
  rw [tendstoInMeasure_iff_norm] at hdiff ⊢
  intro ε hε
  simpa only [ha, hb, sub_zero] using hdiff ε hε

/-- Along triples `(x n i, z n i, y n i)` in a compact set `s` with uniformly vanishing half-step
distances and convergent refined quadratic sums, replacing the symmetric endpoint average by the
intermediate sample `h(X_{z n i})` isolates the alternating half-step quadratic sum
`1 / 2 * ∑ h'(X_{x n i}) * ((X_{z n i} - X_{x n i})² - (X_{y n i} - X_{z n i})²)` up to an error
tending to zero in probability. -/
theorem tendstoInMeasure_sum_midpoint_sub_half_add_sub_half_deriv [IsFiniteMeasure P]
    {X : T → Ω → ℝ} {s : Set T} (hs : IsCompact s)
    {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {k : ℕ → ℕ} {x z y : ℕ → ℕ → T}
    (hx : ∀ n, ∀ i < k n, x n i ∈ s) (hz : ∀ n, ∀ i < k n, z n i ∈ s)
    (hy : ∀ n, ∀ i < k n, y n i ∈ s)
    {δ : ℕ → ℝ} (hδ₁ : ∀ n, ∀ i < k n, dist (z n i) (x n i) ≤ δ n)
    (hδ₂ : ∀ n, ∀ i < k n, dist (y n i) (z n i) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hxmeas : ∀ n, ∀ i < k n, AEStronglyMeasurable (X (x n i)) P)
    (hzmeas : ∀ n, ∀ i < k n, AEStronglyMeasurable (X (z n i)) P)
    (hymeas : ∀ n, ∀ i < k n, AEStronglyMeasurable (X (y n i)) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s)
    {V : Ω → ℝ}
    (hV : TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
      ((X (z n i) ω - X (x n i) ω) ^ 2 + (X (y n i) ω - X (z n i) ω) ^ 2)) atTop V) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
      (h (X (z n i) ω) * (X (y n i) ω - X (x n i) ω) -
        (h (X (x n i) ω) + h (X (y n i) ω)) / 2 * (X (y n i) ω - X (x n i) ω) -
        1 / 2 * deriv h (X (x n i) ω) *
          ((X (z n i) ω - X (x n i) ω) ^ 2 - (X (y n i) ω - X (z n i) ω) ^ 2)))
      atTop (fun _ ↦ 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun ω ↦ ∑ i ∈ range (k n),
      (h (X (z n i) ω) * (X (y n i) ω - X (x n i) ω) -
        (h (X (x n i) ω) + h (X (y n i) ω)) / 2 * (X (y n i) ω - X (x n i) ω) -
        1 / 2 * deriv h (X (x n i) ω) *
          ((X (z n i) ω - X (x n i) ω) ^ 2 - (X (y n i) ω - X (z n i) ω) ^ 2))) P := by
    have : Continuous h := hh.continuous
    have : Continuous (deriv h) := hh.continuous_deriv_one
    refine Finset.aestronglyMeasurable_fun_sum _ fun i hi ↦ ?_
    have := hxmeas n i (mem_range.1 hi)
    have := hzmeas n i (mem_range.1 hi)
    have := hymeas n i (mem_range.1 hi)
    fun_prop
  refine tendstoInMeasure_of_tendsto_of_continuousOn hs
    (ι := fun n ↦ Fin (k n) ⊕ Fin (k n))
    (u := fun n ↦ Sum.elim (fun i ↦ x n i) (fun i ↦ z n i))
    (v := fun n ↦ Sum.elim (fun i ↦ z n i) (fun i ↦ y n i))
    (fun n ↦ Sum.rec (fun i ↦ hx n i i.isLt) (fun i ↦ hz n i i.isLt))
    (fun n ↦ Sum.rec (fun i ↦ hz n i i.isLt) (fun i ↦ hy n i i.isLt))
    (fun n ↦ Sum.rec (fun i ↦ hδ₁ n i i.isLt) (fun i ↦ hδ₂ n i i.isLt))
    hδ hc hV hm ?_
  intro ω idx L R d hLR hd_le hd hQ
  exact TauCeti.tendsto_sum_midpoint_sub_half_add_sub_half_deriv
    (n := fun j ↦ k (idx j))
    (x := fun j i ↦ X (x (idx j) i) ω)
    (z := fun j i ↦ X (z (idx j) i) ω)
    (y := fun j i ↦ X (y (idx j) i) ω)
    (δ := d)
    (fun u _ ↦ (hh.differentiable_one u).hasDerivAt.hasDerivWithinAt)
    hh.continuous_deriv_one.continuousOn
    (Eventually.of_forall fun j i hi ↦ hLR _ (hx (idx j) i hi))
    (Eventually.of_forall fun j i hi ↦ hLR _ (hz (idx j) i hi))
    (Eventually.of_forall fun j i hi ↦ hLR _ (hy (idx j) i hi))
    (Eventually.of_forall fun j i hi ↦ hd_le j (Sum.inl ⟨i, hi⟩))
    (Eventually.of_forall fun j i hi ↦ hd_le j (Sum.inr ⟨i, hi⟩))
    hd hQ.isBoundedUnder_le

end TauCeti.Probability
