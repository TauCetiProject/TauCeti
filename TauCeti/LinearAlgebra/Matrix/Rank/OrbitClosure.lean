/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank.Closed

/-!
# Ranks of powers on closures of conjugacy classes

For a square matrix `Z` and `j r : ℕ`, the condition `rank (Z ^ j) ≤ r` is Zariski closed, and
closed in the usual topology over a field with continuous ring operations and closed points, such
as `ℂ` (`Matrix.rank_pow_le_of_mem_zeroLocus_vanishingIdeal`,
`Matrix.isClosed_setOfPred_rank_pow_le`).

Conjugation does not change the rank of any power, so the ranks of the powers can only drop on the
closure of a conjugacy class: if `Y` lies in the closure of the `GL n K`-conjugacy class of `X`,
then `rank (Y ^ j) ≤ rank (X ^ j)` for every `j`. For nilpotent matrices the ranks of the powers
determine the Jordan type, and these inequalities are the necessary half of the description of
nilpotent orbit closures by the dominance order on partitions. The statements are set-theoretic:
the closures are taken in the `K`-points `Matrix n n K`, with the Zariski closure expressed
through Mathlib's `MvPolynomial.zeroLocus` and `MvPolynomial.vanishingIdeal`.

## Main results

* `Matrix.rank_pow_le_of_mem_zeroLocus_vanishingIdeal_orbit` and
  `Matrix.rank_pow_le_of_mem_closure_orbit`: on the Zariski closure, and on the topological
  closure, of the conjugacy class of `X`, the rank of every power is at most that of `X`.

## References

* M. Gerstenhaber, *On dominance and varieties of commuting matrices*, Ann. of Math. **73**
  (1961), 324–348.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §6.2.
-/

public section

open MvPolynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Zariski

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- On the Zariski closure of the conjugacy class of `X`, the rank of every power is at most the
rank of the same power of `X`. -/
theorem rank_pow_le_of_mem_zeroLocus_vanishingIdeal_orbit {X Y : Matrix n n K}
    (hY : Function.uncurry Y ∈
      zeroLocus K (vanishingIdeal k
        (Function.uncurry '' (MulAction.orbit (ConjAct (GL n K)) X : Set (Matrix n n K)))))
    (j : ℕ) : (Y ^ j).rank ≤ (X ^ j).rank := by
  refine rank_pow_le_of_mem_zeroLocus_vanishingIdeal ?_ hY
  rintro _ ⟨g, rfl⟩
  rw [← smul_pow', rank_conjAct_smul]

end Zariski

section Topological

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]

/-- Over a field with continuous ring operations and closed points, on the closure of the
conjugacy class of `X` the rank of every power is at most the rank of the same power of `X`. -/
theorem rank_pow_le_of_mem_closure_orbit {X Y : Matrix n n K}
    (hY : Y ∈ closure (MulAction.orbit (ConjAct (GL n K)) X)) (j : ℕ) :
    (Y ^ j).rank ≤ (X ^ j).rank := by
  refine closure_minimal ?_ (isClosed_setOfPred_rank_pow_le j _) hY
  rintro _ ⟨g, rfl⟩
  rw [Set.mem_ofPred_eq, ← smul_pow', rank_conjAct_smul]

end Topological

end Matrix
