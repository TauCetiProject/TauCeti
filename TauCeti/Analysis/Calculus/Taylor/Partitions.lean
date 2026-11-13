/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Parameter

/-!
# Accumulated Taylor remainders

Second-order Taylor errors can be summed along finite grids without a bound on the number of
grid points. For a function C³ near a compact interval with bounded third derivative there,
the error is bounded by the largest increment times the sum of squared increments. For a C²
function, local smoothness near a compact set gives a vanishing
coefficient instead. Consequently, if the largest increment tends to zero and the quadratic
sums remain bounded, the accumulated remainder tends to zero. The grids may contain
repetitions or be empty.

These are deterministic estimates for the Taylor-expansion step in change-of-variables
formulas along paths with controlled quadratic sums. Continuous real paths on a compact
metric set satisfy the vanishing-increment condition along vanishing-mesh grids.
The results do not assert convergence of the first- or second-order sums separately.

The one-step expansion uses Mathlib's Taylor theorem with Lagrange remainder.
-/

public section

open Set Filter
open scoped Topology NNReal

namespace TauCeti

/-- The endpoint increment minus the linear and quadratic Taylor sums is the sum of the
individual second-order Taylor remainders. No regularity or ordering of the grid is needed. -/
theorem sub_sum_taylor_two_eq_sum_sub_taylorWithinEval (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) :
    f (x n) - f (x 0) -
      (∑ i ∈ Finset.range n, deriv f (x i) * (x (i + 1) - x i)) -
      1 / 2 * (∑ i ∈ Finset.range n,
        deriv (deriv f) (x i) * (x (i + 1) - x i) ^ 2) =
      ∑ i ∈ Finset.range n,
        (f (x (i + 1)) - taylorWithinEval f 2 univ (x i) (x (i + 1))) := by
  rw [← Finset.sum_range_sub (fun i ↦ f (x i)) n, ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [taylorWithinEval_univ_two]
  ring

/-- A third-derivative bound on an interval containing the grid controls the accumulated
second-order Taylor remainder by the largest increment and the quadratic sum, independently
of the size of the finite grid. Only C³ regularity near that interval is required. -/
theorem abs_sum_sub_taylorWithinEval_two_le {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ z ∈ Icc a b, ContDiffAt ℝ 3 f z)
    {M δ : ℝ} (hM : ∀ z ∈ Icc a b, |iteratedDeriv 3 f z| ≤ M) (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i ≤ n, x i ∈ Icc a b) (hδ : ∀ i < n, |x (i + 1) - x i| ≤ δ) :
    |∑ i ∈ Finset.range n, (f (x (i + 1)) - taylorWithinEval f 2 univ (x i) (x (i + 1)))| ≤
      M / 6 * δ * ∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (hx 0 (Nat.zero_le n)))
  -- Apply the Lagrange remainder on each step, keeping its intermediate point in the interval.
  have hstep i (hi : i ∈ Finset.range n) :
      ‖f (x (i + 1)) - taylorWithinEval f 2 univ (x i) (x (i + 1))‖ ≤
        M / 6 * δ * (x (i + 1) - x i) ^ 2 := by
    rw [Real.norm_eq_abs]
    have hi' := Finset.mem_range.1 hi
    have hsub := uIcc_subset_Icc (hx i hi'.le) (hx (i + 1) hi')
    calc
      _ ≤ M * |x (i + 1) - x i| ^ 3 / 6 := by
        simpa [Nat.factorial] using
          abs_sub_taylorWithinEval_le (n := 2) (fun t ht ↦ hf t (hsub ht))
            (fun t ht ↦ hM t (hsub (uIoo_subset_uIcc_self ht)))
      _ = |x (i + 1) - x i| * (M / 6 * (x (i + 1) - x i) ^ 2) := by
        rw [pow_succ, sq_abs]
        ring
      _ ≤ δ * (M / 6 * (x (i + 1) - x i) ^ 2) :=
        mul_le_mul_of_nonneg_right (hδ i hi') (by positivity)
      _ = _ := by ring
  -- Mathlib's finite-sum bound combines the per-step quadratic estimates.
  simpa only [Real.norm_eq_abs, ← Finset.mul_sum] using
    norm_sum_le_of_le (Finset.range n) hstep

/-- The sum of the first- and second-order Taylor terms approximates the endpoint increment
for functions C² near a fixed compact set and grids eventually confined to it, with
vanishing increments and eventually bounded quadratic sums. The grid family may be indexed
by any filter. No nesting, ordering, or bound on the number of grid points is required. -/
theorem tendsto_sub_sum_taylor_two {f : ℝ → ℝ} {s : Set ℝ} {K : ℝ}
    (hf : ∀ z ∈ s, ContDiffAt ℝ 2 f z) (hs : IsCompact s)
    {ι : Type*} {l : Filter ι} {x : ι → ℕ → ℝ} {n : ι → ℕ} {δ : ι → ℝ}
    (hx : ∀ᶠ k in l, ∀ i ≤ n k, x k i ∈ s)
    (hδ : ∀ᶠ k in l, ∀ i < n k, |x k (i + 1) - x k i| ≤ δ k)
    (hδ0 : Tendsto δ l (𝓝 0))
    (hQ : ∀ᶠ k in l, ∑ i ∈ Finset.range (n k), (x k (i + 1) - x k i) ^ 2 ≤ K) :
    Tendsto (fun k ↦ f (x k (n k)) - f (x k 0) -
      (∑ i ∈ Finset.range (n k), deriv f (x k i) * (x k (i + 1) - x k i)) -
      1 / 2 * ∑ i ∈ Finset.range (n k),
        deriv (deriv f) (x k i) * (x k (i + 1) - x k i) ^ 2) l (𝓝 0) := by
  simp_rw [sub_sum_taylor_two_eq_sum_sub_taylorWithinEval]
  -- The compact set may have gaps where the function is not smooth, so use the compact-set
  -- estimate rather than the parameter-family estimate on a containing interval.
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨η, hη, hTaylor⟩ := exists_pos_forall_abs_sub_taylorWithinEval_two_le_of_isCompact
    hf hs (div_pos hε (by positivity : 0 < max K 0 + 1))
  filter_upwards [(tendsto_order.1 hδ0).2 η hη, hx, hδ, hQ] with k hk hxk hδk hQk
  have hstep i (hi : i ∈ Finset.range (n k)) :
      ‖f (x k (i + 1)) - taylorWithinEval f 2 univ (x k i) (x k (i + 1))‖ ≤
        ε / (max K 0 + 1) * (x k (i + 1) - x k i) ^ 2 := by
    have hi' := Finset.mem_range.1 hi
    simpa only [Real.norm_eq_abs] using
      hTaylor _ (hxk i hi'.le) _ (hxk (i + 1) hi') ((hδk i hi').trans_lt hk)
  have hbound : |∑ i ∈ Finset.range (n k),
      (f (x k (i + 1)) - taylorWithinEval f 2 univ (x k i) (x k (i + 1)))| ≤
      ε / (max K 0 + 1) * max K 0 := by
    calc
      _ ≤ ε / (max K 0 + 1) *
          ∑ i ∈ Finset.range (n k), (x k (i + 1) - x k i) ^ 2 := by
        simpa only [Real.norm_eq_abs, ← Finset.mul_sum] using
          norm_sum_le_of_le (Finset.range (n k)) hstep
      _ ≤ _ := by gcongr; exact hQk.trans (le_max_left _ _)
  rw [Real.dist_eq, sub_zero]
  apply hbound.trans_lt
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < max K 0 + 1)]
  linarith


/-- Along grids eventually in a compact metric set with eventually controlled vanishing mesh
and bounded quadratic sums, the second-order Taylor expansion along a continuous real path has
vanishing accumulated remainder. The function need only be C² at the path values in that set.
No variation bound on the path is assumed. -/
theorem tendsto_sub_sum_taylor_two_of_continuousOn {f : ℝ → ℝ}
    {α : Type*} [PseudoMetricSpace α] {g : α → ℝ} {s : Set α}
    (hf : ∀ x ∈ s, ContDiffAt ℝ 2 f (g x)) (hs : IsCompact s) (hg : ContinuousOn g s)
    {ι : Type*} {l : Filter ι}
    {n : ι → ℕ} {t : ι → ℕ → α} {δ : ι → ℝ} {K : ℝ}
    (ht : ∀ᶠ k in l, ∀ i ≤ n k, t k i ∈ s)
    (hmesh : ∀ᶠ k in l, ∀ i < n k, dist (t k (i + 1)) (t k i) ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0))
    (hQ : ∀ᶠ k in l, ∑ i ∈ Finset.range (n k), (g (t k (i + 1)) - g (t k i)) ^ 2 ≤ K) :
    Tendsto (fun k ↦ f (g (t k (n k))) - f (g (t k 0)) -
      (∑ i ∈ Finset.range (n k), deriv f (g (t k i)) *
        (g (t k (i + 1)) - g (t k i))) -
      1 / 2 * ∑ i ∈ Finset.range (n k), deriv (deriv f) (g (t k i)) *
        (g (t k (i + 1)) - g (t k i)) ^ 2) l (𝓝 0) := by
  let D (k : ι) : ℝ≥0 := (Finset.range (n k)).sup fun i ↦
    ‖g (t k (i + 1)) - g (t k i)‖₊
  have hD : Tendsto D l (𝓝 0) := by
    apply tendsto_order.2
    refine ⟨fun a ha ↦ (not_lt_of_ge (zero_le : 0 ≤ a) ha).elim, fun ε hε ↦ ?_⟩
    obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuousOn_iff.1
      (hs.uniformContinuousOn_of_continuous hg) (ε : ℝ) (NNReal.coe_pos.2 hε)
    filter_upwards [hδ.eventually_lt_const hη, ht, hmesh] with k hk htk hmeshk
    apply Finset.sup_lt_iff hε |>.2
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [← NNReal.coe_lt_coe]
    push_cast
    rw [← dist_eq_norm]
    exact hηg _ (htk (i + 1) hi') _ (htk i hi'.le)
      ((hmeshk i hi').trans_lt hk)
  apply tendsto_sub_sum_taylor_two
    (fun z hz ↦ by obtain ⟨x, hx, rfl⟩ := hz; exact hf x hx)
    (hs.image_of_continuousOn hg) (K := K)
    (δ := fun k ↦ (D k : ℝ))
    (ht.mono fun k htk i hi ↦ mem_image_of_mem g (htk i hi))
    (Eventually.of_forall fun k i hi ↦ ?_)
    (by simpa only [Function.comp_def, NNReal.coe_zero] using
      NNReal.continuous_coe.tendsto 0 |>.comp hD) hQ
  rw [← Real.norm_eq_abs]
  dsimp only [D]
  have hle := NNReal.coe_le_coe.2 (Finset.le_sup (f := fun i ↦
    ‖g (t k (i + 1)) - g (t k i)‖₊) (Finset.mem_range.2 hi))
  push_cast at hle
  exact hle

end TauCeti
