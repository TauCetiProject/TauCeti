/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Equicontinuous curves in `ℓ²` without compact closure

The Arzelà–Ascoli theorem `ArzelaAscoli.isCompact_closure_of_equicontinuous` asks that the values
of the maps at each point lie in a common compact set. This hypothesis cannot be replaced by
equicontinuity and a common starting point when the target is not proper. The curves
`γₙ(t) = t • eₙ`, `t ∈ [0, 1]`, along the standard basis vectors of `ℓ²` are `1`-Lipschitz and all
start at `0`, but no subsequence converges uniformly, because the endpoints `eₙ` stay at distance
at least `1` from each other.

## Main results

* `TauCeti.exists_lipschitzWith_one_not_isCompact_closure_range`: the curves `t • eₙ` in `ℓ²`.
-/

public section

open Set

namespace TauCeti

/-- **Equicontinuity and a common starting point do not give compactness.** The curves
`γₙ(t) = t • eₙ`, `t ∈ [0, 1]`, along the standard basis vectors `eₙ` of `ℓ²` are `1`-Lipschitz and
all start at `0`, but they form a set without compact closure in `C([0, 1], ℓ²)`, because their
endpoints are at distance at least `1` from each other. The pointwise compactness hypothesis of
`ArzelaAscoli.isCompact_closure_of_equicontinuous` therefore cannot be dropped. -/
theorem exists_lipschitzWith_one_not_isCompact_closure_range :
    ∃ γ : ℕ → C(Icc (0 : ℝ) 1, lp (fun _ : ℕ ↦ ℝ) 2),
      (∀ n, LipschitzWith 1 (γ n)) ∧ (∀ n, γ n ⟨0, left_mem_Icc.mpr zero_le_one⟩ = 0) ∧
        ¬ IsCompact (closure (range γ)) := by
  classical
  set e : ℕ → lp (fun _ : ℕ ↦ ℝ) 2 := fun n ↦ lp.single 2 n 1 with he
  have he_norm : ∀ n, ‖e n‖ = 1 := fun n ↦ by simp [he, lp.norm_single]
  -- Distinct basis vectors are at distance at least `1`: compare their `n`-th coordinates.
  have he_dist : ∀ n m, n ≠ m → 1 ≤ dist (e n) (e m) := by
    intro n m hnm
    have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (e n - e m) n
    simpa [he, dist_eq_norm, lp.single_apply, Pi.single_apply, hnm] using this
  refine ⟨fun n ↦ ⟨fun t ↦ (t : ℝ) • e n, by fun_prop⟩, fun n ↦ ?_, fun n ↦ by simp, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    simp [dist_eq_norm, ← sub_smul, norm_smul, he_norm, Subtype.dist_eq]
  · intro hc
    obtain ⟨g, -, φ, hφ, hlim⟩ := hc.tendsto_subseq fun n ↦ subset_closure ⟨n, rfl⟩
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq 1 one_pos
    have hlt := hN N le_rfl (N + 1) N.le_succ
    have hle := ContinuousMap.dist_apply_le_dist (f := (⟨fun t ↦ (t : ℝ) • e (φ N), by fun_prop⟩ :
      C(Icc (0 : ℝ) 1, lp (fun _ : ℕ ↦ ℝ) 2)))
      (g := ⟨fun t ↦ (t : ℝ) • e (φ (N + 1)), by fun_prop⟩) ⟨1, right_mem_Icc.mpr zero_le_one⟩
    have h1 := he_dist (φ N) (φ (N + 1)) (hφ N.lt_succ_self).ne
    simp only [ContinuousMap.coe_mk, one_smul] at hle
    exact absurd (h1.trans hle) (not_le.mpr hlt)

end TauCeti
