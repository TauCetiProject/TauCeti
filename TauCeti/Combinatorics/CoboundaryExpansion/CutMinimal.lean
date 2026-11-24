/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal.Basic
public import TauCeti.Combinatorics.SimpleGraph.OddTriple.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.SwapGauge
import Mathlib.Tactic.Positivity

/-!
# Cut-minimal Cheeger upper bounds

For a cut-minimal graph `G` on a finite linear order `V` with at least one edge and any finite
symmetric group `Equiv.Perm α`, choosing a transposition `t = Equiv.swap a b` (when `α` is
nontrivial; otherwise `h1 = 0`) gives a cochain `G.toCochain ht.mul_self` with moved-point defect
`2 * #G.oddTripleFinset` (`SimpleGraph.defect_movedNorm_toCochain`) and gauge distance
`2 * #G.edgeFinset` (`SimpleGraph.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq`). Hence:

* `SimpleGraph.h1_complete_movedNorm_le_of_isCutMinimal`: for a cut-minimal `G` with an edge and
  any finite `α`,
  `h1 (complete V) (movedNorm α) ≤ #G.oddTripleFinset / #G.edgeFinset`.

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Section 2.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792,
  Corollary 7 and Theorem 8.
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: this file adapts the cut-minimal upper bound from `CoboundaryK3/Staircase.lean`,
  using `SimpleGraph.toCochain`.
-/

public section

namespace SimpleGraph

open Finset Equiv TauCeti TauCeti.TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- **Cut-minimal graphs bound `h1` for every finite symmetric group.** For a cut-minimal graph
`G` on `V` with at least one edge,
`h1 (complete V) (movedNorm α) ≤ #G.oddTripleFinset / #G.edgeFinset`. -/
theorem h1_complete_movedNorm_le_of_isCutMinimal {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsCutMinimal)
    (hE : 0 < #G.edgeFinset) :
    h1 (complete V) (Perm.movedNorm α) ≤
      (#G.oddTripleFinset : ℝ) / #G.edgeFinset := by
  rcases subsingleton_or_nontrivial α with _ | _
  · rw [h1_subsingleton]
    positivity
  · obtain ⟨a, b, hab⟩ := exists_pair_ne α
    have ht : (swap a b).IsSwap := Perm.swap_isSwap_iff.mpr hab
    have hE' : (0 : ℝ) < 2 * #G.edgeFinset := by positivity
    have hgd : (G.toCochain ht.mul_self).gaugeDist (Perm.movedNorm α) = 2 * #G.edgeFinset :=
      (G.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq ht).mp hG
    refine (h1_le_div (hgd ▸ hE')).trans_eq ?_
    rw [G.defect_movedNorm_toCochain ht, hgd]
    exact mul_div_mul_left _ _ two_ne_zero

end SimpleGraph
