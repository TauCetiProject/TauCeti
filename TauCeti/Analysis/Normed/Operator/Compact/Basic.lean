/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact operators and bounded sequences

This file records sequential consequences of compactness for bounded sequences in seminormed
spaces. These give the subsequence and separation arguments used in Riesz theory for compact
perturbations of the identity.

## Main declarations

* `IsCompactOperator.exists_subseq_tendsto`: a compact operator sends a bounded sequence
  to a sequence with a convergent subsequence.
* `IsCompactOperator.exists_dist_lt_of_norm_le`: a compact operator cannot keep the
  images of a bounded sequence pairwise separated.
-/

public section

namespace IsCompactOperator

open Filter
open scoped Topology

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {K : X →ₗ[𝕜] Y}
variable {R : ℝ} {u : ℕ → X}

/-- A compact operator sends a bounded sequence to a sequence with a convergent subsequence. -/
theorem exists_subseq_tendsto (hK : IsCompactOperator K) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (y : Y) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (fun k => K (u (ψ k))) atTop (𝓝 y) := by
  obtain ⟨S, hS, hSsub⟩ := hK.image_closedBall_subset_compact R
  obtain ⟨y, -, ψ, hψ, hψy⟩ :=
    hS.tendsto_subseq fun n => hSsub ⟨u n, by simpa using hu n, rfl⟩
  exact ⟨y, ψ, hψ, hψy⟩

/-- A compact operator cannot keep the images of a bounded sequence pairwise separated: two
distinct indices always have images within any prescribed positive distance. -/
theorem exists_dist_lt_of_norm_le (hK : IsCompactOperator K) (hu : ∀ n, ‖u n‖ ≤ R) {ε : ℝ}
    (hε : 0 < ε) : ∃ m n, m ≠ n ∧ dist (K (u m)) (K (u n)) < ε := by
  obtain ⟨y, ψ, hψ, hψy⟩ := hK.exists_subseq_tendsto hu
  have hcauchy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  exact ⟨ψ (N + 1), ψ N, by simp [hψ.injective.eq_iff], hN (N + 1) (Nat.le_succ N)⟩

end IsCompactOperator

end
