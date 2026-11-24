/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The Neumann series of a continuous additive endomorphism

For a continuous additive endomorphism `N` of a Hausdorff topological additive group, if the
series `y = ∑ Nⁿ x` of iterates converges then `y - N y = x`. So `x ↦ ∑ Nⁿ x` is a right inverse
of `1 - N` wherever the series converges. This is the operator form of the geometric-series
identity `(1 - a) ∑ aⁿ = 1`, for maps that are not multiplication by an element of a ring. No
nonarchimedean hypothesis is needed; the complete nonarchimedean case, where convergence follows
from the iterates tending to zero, is
`NonarchimedeanAddGroup.tsum_iterate_sub_apply_tsum_iterate`.

## Main results

* `Summable.tsum_iterate_sub_apply_tsum_iterate`: if `y = ∑ Nⁿ x` converges then `y - N y = x`.
-/

public section

variable {G F : Type*} [AddCommGroup G] [FunLike F G G] [AddMonoidHomClass F G G]

/-- **The Neumann series of a continuous additive endomorphism.** If the series `y = ∑ Nⁿ x` of
iterates of a continuous additive endomorphism `N` converges in a Hausdorff topological additive
group, then `y - N y = x`. For `N` multiplication by a topologically nilpotent `a` this is the
identity `(1 - a) ∑ aⁿ = 1` behind `IsTopologicallyNilpotent.isUnit_one_sub`. -/
theorem Summable.tsum_iterate_sub_apply_tsum_iterate [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] {N : F} (hN : Continuous N) {x : G}
    (hs : Summable fun n ↦ N^[n] x) :
    ∑' n, N^[n] x - N (∑' n, N^[n] x) = x := by
  have hmap : N (∑' n, N^[n] x) = ∑' n, N^[n + 1] x := by
    rw [(hs.hasSum.map N hN).tsum_eq.symm]
    simp only [Function.comp_def, Function.iterate_succ_apply']
  rw [hmap, hs.tsum_eq_zero_add, Function.iterate_zero_apply, add_sub_cancel_right]

end
