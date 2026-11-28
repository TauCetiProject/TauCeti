/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weak-star convergent subsequences on separable subspaces

The dual unit ball of a nonseparable normed space need not be weak-star sequentially compact. Yet
every bounded sequence of continuous linear functionals on a real or complex normed space has a
subsequence that converges pointwise on any prescribed separable set `s`, and even on its closed
linear span, to a continuous linear functional obeying the same norm bound
(`TauCeti.exists_strictMono_tendsto_apply_of_isSeparable`).

The proof restricts the functionals to the closed linear span of `s`, which is separable, applies
the sequential Banach–Alaoglu theorem `WeakDual.isSeqCompact_closedBall` there, and extends the
limit back to the whole space by the Hahn–Banach theorem `exists_extension_norm_eq`.

This separable reduction is the compactness step in the Orlicz–Pettis theorem.

## References

* J. Diestel, *Sequences and Series in Banach Spaces*, Graduate Texts in Mathematics 92,
  Springer, 1984, Chapter II.
-/

public section

open Filter Set Topology TopologicalSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A sequence of continuous linear functionals bounded by `C` has a subsequence that converges
pointwise on the closed linear span of a given separable set `s` to a continuous linear functional
of norm at most `C`. -/
theorem exists_strictMono_tendsto_apply_of_isSeparable {g : ℕ → StrongDual 𝕜 E} {C : ℝ}
    (hg : ∀ k, ‖g k‖ ≤ C) {s : Set E} (hs : IsSeparable s) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ W : StrongDual 𝕜 E, ‖W‖ ≤ C ∧
      ∀ y ∈ (Submodule.span 𝕜 s).topologicalClosure,
        Tendsto (fun j ↦ g (ψ j) y) atTop (𝓝 (W y)) := by
  set X₀ := (Submodule.span 𝕜 s).topologicalClosure
  have : SeparableSpace X₀ := by
    have : IsSeparable (X₀ : Set E) := by
      rw [Submodule.topologicalClosure_coe]
      exact (hs.span (R := 𝕜)).closure
    exact this.separableSpace
  -- Restrict the functionals to `X₀` and extract a weak-star convergent subsequence.
  let w : ℕ → WeakDual 𝕜 X₀ := fun k ↦ StrongDual.toWeakDual ((g k).comp X₀.subtypeL)
  have hball (k : ℕ) : w k ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    simp only [Set.mem_preimage, mem_closedBall_zero_iff]
    refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hg k)) fun z ↦ ?_
    simpa [w] using (g k).le_of_opNorm_le (hg k) (z : E)
  obtain ⟨w₀, hw₀, ψ, hψ, hlim⟩ := WeakDual.isSeqCompact_closedBall 𝕜 X₀ 0 C hball
  -- Extend the limit to `E`.
  obtain ⟨W, hW, hWn⟩ := exists_extension_norm_eq X₀ (WeakDual.toStrongDual w₀)
  refine ⟨ψ, hψ, W, hWn ▸ mem_closedBall_zero_iff.1 hw₀, fun y hy ↦ ?_⟩
  have hWy : W y = w₀ ⟨y, hy⟩ := by simpa using hW ⟨y, hy⟩
  rw [hWy]
  simpa [w, Function.comp_def] using
    ((WeakDual.eval_continuous (⟨y, hy⟩ : X₀)).tendsto w₀).comp hlim

end TauCeti
