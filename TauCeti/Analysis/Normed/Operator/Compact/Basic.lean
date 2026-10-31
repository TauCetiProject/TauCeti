/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Compact operators on quotients and bounded sequences

This file records sequential consequences of compactness for bounded sequences in seminormed
spaces. These give the subsequence and separation arguments used in Riesz theory for compact
perturbations of the identity. It also shows that a compact operator descends to a compact
operator on the quotient by a submodule of its kernel.

## Main declarations

* `IsCompactOperator.exists_subseq_tendsto`: a compact operator sends a bounded sequence
  to a sequence with a convergent subsequence.
* `IsCompactOperator.exists_dist_lt_of_norm_le`: a compact operator cannot keep the
  images of a bounded sequence pairwise separated.
* `IsCompactOperator.liftQL`: the operator induced by a compact operator on a quotient by a
  submodule of its kernel is compact.
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

section Quotient

variable {R₁ R₂ M N : Type*} [Ring R₁] [Ring R₂] {σ : R₁ →+* R₂} [AddCommGroup M] [Module R₁ M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [AddCommGroup N] [Module R₂ N]
  [TopologicalSpace N]

/-- A compact operator descends to a compact operator on the quotient by a submodule of its
kernel. -/
theorem liftQL {S : Submodule R₁ M} {f : M →SL[σ] N} (hf : IsCompactOperator f)
    (h : S ≤ f.ker) : IsCompactOperator (S.liftQL f h) := by
  -- The quotient map is open, so it carries a neighbourhood of `0` that `f` maps into a compact
  -- set `C` to a neighbourhood of `0` that the induced map sends into `C`.
  obtain ⟨C, hC, hfC⟩ := hf
  refine ⟨C, hC, Filter.mem_of_superset (x := S.mkQ '' (f ⁻¹' C)) ?_ ?_⟩
  · simpa using S.isOpenMap_mkQ.image_mem_nhds hfC
  · rintro _ ⟨m, hm, rfl⟩
    simpa using hm

end Quotient

end IsCompactOperator

end
