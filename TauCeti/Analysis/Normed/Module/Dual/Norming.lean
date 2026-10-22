/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Norming sequences for separable sets

On a separable subset `s` of a seminormed space over `ℝ` or `ℂ`, the norm is a supremum over
countably many continuous linear functionals of norm at most one:
`‖x‖ = ⨆ n, ‖f n x‖` for every `x ∈ s`. The functionals are Hahn–Banach norming functionals of
the points of a countable set whose closure contains `s`.

A norming sequence for a separable subspace separates its points. This is the separable
reduction used in weak-topology arguments: such a sequence separates the points of a weakly
compact subset of a separable closed subspace, so that subset is weakly metrizable.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, the proof of Theorem 2.8.6.
-/

public section

open Metric Set

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace TopologicalSpace.IsSeparable

variable (𝕜) in
/-- A separable set admits a norming sequence of continuous linear functionals: a sequence of
functionals of norm at most one whose absolute values have supremum `‖x‖` at each point `x`
of the set. -/
theorem exists_norming_seq {s : Set E} (hs : IsSeparable s) :
    ∃ f : ℕ → StrongDual 𝕜 E, (∀ n, ‖f n‖ ≤ 1) ∧ ∀ x ∈ s, ‖x‖ = ⨆ n, ‖f n x‖ := by
  obtain ⟨c, hc, hsc⟩ := hs
  -- Adding `0` makes the countable set nonempty, so that it can be enumerated by `ℕ`.
  obtain ⟨y, hy⟩ := (hc.insert 0).exists_eq_range (insert_nonempty 0 c)
  choose f hf hfy using fun n ↦ exists_dual_vector'' 𝕜 (y n)
  refine ⟨f, hf, fun x hx ↦ ?_⟩
  have hle (n : ℕ) (z : E) : ‖f n z‖ ≤ ‖z‖ :=
    ((f n).le_opNorm z).trans (mul_le_of_le_one_left (norm_nonneg z) (hf n))
  have hbdd : BddAbove (range fun n ↦ ‖f n x‖) := ⟨‖x‖, forall_mem_range.mpr (hle · x)⟩
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ ?_) (ciSup_le (hle · x))
  have hxy : x ∈ closure (range y) := hy ▸ closure_mono (subset_insert 0 c) (hsc hx)
  obtain ⟨n, hn⟩ := mem_closure_range_iff.mp hxy (ε / 2) (half_pos hε)
  rw [dist_eq_norm] at hn
  -- `f n` norms `y n`, which is within `ε / 2` of `x`.
  have hyn : ‖y n‖ ≤ ‖f n x‖ + ‖x - y n‖ := calc
    ‖y n‖ = ‖f n (y n)‖ := by rw [hfy, RCLike.norm_ofReal, abs_norm]
    _ = ‖f n x - f n (x - y n)‖ := by rw [map_sub, sub_sub_cancel]
    _ ≤ ‖f n x‖ + ‖f n (x - y n)‖ := norm_sub_le _ _
    _ ≤ ‖f n x‖ + ‖x - y n‖ := by grw [hle n (x - y n)]
  calc ‖x‖ ≤ ‖y n‖ + ‖x - y n‖ := norm_le_norm_add_norm_sub' x (y n)
    _ < ‖f n x‖ + ε := by linarith
    _ ≤ (⨆ n, ‖f n x‖) + ε := by grw [le_ciSup hbdd n]

end TopologicalSpace.IsSeparable
