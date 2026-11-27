/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Dominated convergence for `ℓ^r` norms and suprema

Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) passes a limit through a series whose
terms are dominated by a summable sequence. This file records two consequences for families
`b t j ≥ 0` of real numbers dominated by a sequence `a j` and tending to `0` termwise:

* `TauCeti.tendsto_tsum_rpow_rpow_of_dominated`: if `∑ⱼ (a j)^r < ∞`, `r > 0`, then the `ℓ^r` norms
  `(∑ⱼ (b t j)^r)^{1/r}` tend to `0`;
* `TauCeti.tendsto_iSup_of_dominated`: if `a j → 0`, then the suprema `⨆ⱼ b t j` tend to `0`.

Applied to the weighted Littlewood–Paley blocks of `T t u - u`, these show that operators `T t`
converging blockwise and bounded blockwise converge strongly on the Besov spaces `B^s_{p,q}` with
`q < ∞` and on the little Besov spaces.
-/

public section

open Filter Topology in
/-- **Dominated convergence for `ℓ^r` norms.** If `0 ≤ b t j ≤ a j` with `∑ⱼ (a j)^r < ∞`, `r > 0`,
and each `b t j → 0` along `l`, then `(∑ⱼ (b t j)^r)^{1/r} → 0` along `l`. Applied to the weighted
blocks of `T t u - u`, this is strong continuity of a family of operators `T t` on a Besov space
with `q < ∞` that converge blockwise and are bounded blockwise. -/
theorem TauCeti.tendsto_tsum_rpow_rpow_of_dominated {α ι : Type*} {l : Filter α}
    {b : α → ι → ℝ} {a : ι → ℝ} {r : ℝ} (hr : 0 < r) (hb0 : ∀ t j, 0 ≤ b t j)
    (hba : ∀ t j, b t j ≤ a j) (hb : ∀ j, Tendsto (fun t ↦ b t j) l (𝓝 0))
    (ha : Summable fun j ↦ a j ^ r) :
    Tendsto (fun t ↦ (∑' j, b t j ^ r) ^ (1 / r)) l (𝓝 0) := by
  have hsum : Tendsto (fun t ↦ ∑' j, b t j ^ r) l (𝓝 (∑' _ : ι, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence ha (fun j ↦ ?_) (.of_forall fun t j ↦ ?_)
    · have h := (hb j).rpow_const (Or.inr hr.le)
      rwa [Real.zero_rpow hr.ne'] at h
    · rw [Real.norm_of_nonneg (Real.rpow_nonneg (hb0 t j) r)]
      exact Real.rpow_le_rpow (hb0 t j) (hba t j) hr.le
  rw [tsum_zero] at hsum
  have h := hsum.rpow_const (Or.inr (one_div_pos.2 hr).le)
  rwa [Real.zero_rpow (one_div_pos.2 hr).ne'] at h

open Filter Topology in
/-- **Dominated convergence for `ℓ^∞` norms of null sequences.** If `0 ≤ b t j ≤ a j` with
`a j → 0` as `j → ∞`, and each `b t j → 0` along `l`, then `⨆ⱼ b t j → 0` along `l`: beyond some
`N` every `b t j` is small uniformly in `t`, and the finitely many others converge. -/
theorem TauCeti.tendsto_iSup_of_dominated {α : Type*} {l : Filter α} {b : α → ℕ → ℝ}
    {a : ℕ → ℝ} (hb0 : ∀ t j, 0 ≤ b t j) (hba : ∀ t j, b t j ≤ a j)
    (hb : ∀ j, Tendsto (fun t ↦ b t j) l (𝓝 0)) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun t ↦ ⨆ j, b t j) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (half_pos hε)
  have hlow : ∀ᶠ t in l, ∀ j ∈ Finset.range N, b t j < ε / 2 :=
    (Finset.range N).eventually_all.2 fun j _ ↦ (hb j).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hlow] with t ht
  rw [Real.dist_0_eq_abs, abs_of_nonneg (Real.iSup_nonneg (hb0 t))]
  refine lt_of_le_of_lt (ciSup_le fun j ↦ ?_) (half_lt_self hε)
  rcases lt_or_ge j N with hj | hj
  · exact (ht j (Finset.mem_range.2 hj)).le
  · have hNj := hN j hj
    rw [Real.dist_0_eq_abs] at hNj
    exact (hba t j).trans ((le_abs_self _).trans hNj.le)
