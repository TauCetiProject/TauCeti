/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Normed.Group.Tannery
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.LocallyConvex.WithSeminorms

/-!
# Dominated convergence for series in `𝓓_K`

Let `v m` be smooth functions supported in a compact set `K`, and let the coefficients `c x m`
depend on a parameter `x`. If for every order `k` the products `‖c x m‖ N_k (v m)` of the
coefficients with the `k`-th seminorms are dominated by a summable sequence `b k m`, uniformly in
`x`, and each coefficient converges, then the series `∑ m, c x m • v m` converges in `𝓓_K`, and its
sum converges to the sum of the limit series
(`ContDiffMapSupportedIn.tendsto_tsum_smul_of_dominated`).

With the parameter in a topological space, this gives the continuity of such series; with the
coefficients tending to zero at infinity, it gives a compact set `{0} ∪ {∑ m, c x m • v m}` of
smooth functions supported in `K`, as used for the Fourier series of test functions with modulated
cutoffs `v m`.
-/

public section

open Filter Topology
open scoped Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [CompleteSpace F] {K : TopologicalSpace.Compacts E}

/-- A series `∑ m, c m • v m` in `𝓓_K` whose terms have seminorms dominated by summable sequences
is summable. -/
theorem summable_smul_of_le {ι : Type*} {v : ι → 𝓓_{K}(E, F)} {c : ι → ℂ} {b : ℕ → ι → ℝ}
    (hb : ∀ k, Summable (b k)) (hc : ∀ k m, ‖c m‖ * N[ℂ]_{K, k} (v m) ≤ b k m) :
    Summable fun m ↦ c m • v m :=
  (ContDiffMapSupportedIn.withSeminorms ℂ E F ⊤ K).summable_of_summable_seminorm fun k ↦
    (hb k).of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) fun m ↦ by
      rw [map_smul_eq_mul]
      exact hc k m

/-- **Dominated convergence for series in `𝓓_K`.** If the products `‖c x m‖ N_k (v m)` are
dominated by summable sequences `b k m`, eventually along a filter `l`, and so are the products
`‖c₀ m‖ N_k (v m)`, and each coefficient `c x m` tends to `c₀ m`, then `∑ m, c x m • v m` tends to
`∑ m, c₀ m • v m` in `𝓓_K`. -/
theorem tendsto_tsum_smul_of_dominated {X ι : Type*} {l : Filter X} {v : ι → 𝓓_{K}(E, F)}
    {c : X → ι → ℂ} {c₀ : ι → ℂ} {b : ℕ → ι → ℝ} (hb : ∀ k, Summable (b k))
    (hc : ∀ᶠ x in l, ∀ k m, ‖c x m‖ * N[ℂ]_{K, k} (v m) ≤ b k m)
    (hc₀ : ∀ k m, ‖c₀ m‖ * N[ℂ]_{K, k} (v m) ≤ b k m)
    (hlim : ∀ m, Tendsto (fun x ↦ c x m) l (𝓝 (c₀ m))) :
    Tendsto (fun x ↦ ∑' m, c x m • v m) l (𝓝 (∑' m, c₀ m • v m)) := by
  have hw := ContDiffMapSupportedIn.withSeminorms ℂ E F ⊤ K
  rw [hw.tendsto_nhds]
  intro k ε hε
  -- Where the bounds hold, the seminorms of the differences of the terms are dominated by `2 b k`.
  have hdom {x : X} (hx : ∀ k m, ‖c x m‖ * N[ℂ]_{K, k} (v m) ≤ b k m) (m : ι) :
      ‖c x m - c₀ m‖ * N[ℂ]_{K, k} (v m) ≤ 2 * b k m :=
    calc ‖c x m - c₀ m‖ * N[ℂ]_{K, k} (v m)
        ≤ (‖c x m‖ + ‖c₀ m‖) * N[ℂ]_{K, k} (v m) := by gcongr; exact norm_sub_le _ _
      _ ≤ b k m + b k m := by rw [add_mul]; exact add_le_add (hx k m) (hc₀ k m)
      _ = 2 * b k m := by ring
  have hconv : Tendsto (fun x ↦ ∑' m, ‖c x m - c₀ m‖ * N[ℂ]_{K, k} (v m)) l (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence
      (f := fun x m ↦ ‖c x m - c₀ m‖ * N[ℂ]_{K, k} (v m)) (g := fun _ ↦ (0 : ℝ))
      (bound := fun m ↦ 2 * b k m) ((hb k).mul_left 2)
      (fun m ↦ by simpa using (((hlim m).sub_const (c₀ m)).norm.mul_const (N[ℂ]_{K, k} (v m))))
      (by
        filter_upwards [hc] with x hx m
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hdom hx m)
    simpa using h
  filter_upwards [hc, hconv.eventually (gt_mem_nhds hε)] with x hx hxε
  rw [← (summable_smul_of_le hb hx).tsum_sub (summable_smul_of_le hb hc₀)]
  simp_rw [← sub_smul]
  refine (Seminorm.map_tsum_le (hw.continuous_seminorm k) ?_).trans_lt ?_
  · refine ((hb k).mul_left 2).of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) fun m ↦ ?_
    rw [map_smul_eq_mul]
    exact hdom hx m
  · simpa only [map_smul_eq_mul] using hxε

end ContDiffMapSupportedIn
