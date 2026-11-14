/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Sums over selected homogeneous components

For an internal module grading, the sum of the pieces indexed by any set is
characterized by vanishing of all excluded components. Such sums are stable
under homogeneous projections. These criteria detect membership and homogeneity
of `TauCeti.supportedLieSubalgebra`.

We use Mathlib's `DirectSum.decompose_of_mem_ne` and
`DirectSum.sum_support_decompose` to detect and reconstruct the allowed support.

Adapted from `Mei/Algebra/DirectSum/Supported.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original notice: Copyright (c) 2026 Mei contributors. All rights reserved.
Authors: Codex.
-/

public section

namespace TauCeti.DirectSum

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M) [DecidableEq ι] [_root_.DirectSum.Decomposition ℳ]
  (S : Set ι)

/-- Membership in a sum of selected pieces means that every excluded component vanishes. -/
theorem mem_iSup_iff_decompose_eq_zero {x : M} :
    x ∈ ⨆ i : S, ℳ i ↔
      ∀ i, i ∉ S → (_root_.DirectSum.decompose ℳ x i : M) = 0 := by
  classical
  constructor
  · intro hx i hi
    exact Submodule.iSup_induction _
      (motive := fun x => (_root_.DirectSum.decompose ℳ x i : M) = 0) hx
      (fun j x hx => _root_.DirectSum.decompose_of_mem_ne ℳ hx
        (fun h => hi (h ▸ j.property)))
      (by simp) (fun x y hx hy => by simp [hx, hy])
  · intro hx
    rw [← _root_.DirectSum.sum_support_decompose ℳ x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ S
    · exact Submodule.mem_iSup_of_mem ⟨i, hi⟩
        (_root_.DirectSum.decompose ℳ x i).property
    · rw [hx i hi]
      exact Submodule.zero_mem _

/-- A sum of selected homogeneous pieces is stable under homogeneous projections. -/
theorem isHomogeneous_iSup :
    _root_.DirectSum.SetLike.IsHomogeneous ℳ (⨆ i : S, ℳ i) := by
  classical
  intro i x hx
  by_cases hi : i ∈ S
  · exact Submodule.mem_iSup_of_mem ⟨i, hi⟩
      (_root_.DirectSum.decompose ℳ x i).property
  · rw [(mem_iSup_iff_decompose_eq_zero ℳ S).mp hx i hi]
    exact Submodule.zero_mem _

end TauCeti.DirectSum
