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
import TauCeti.Combinatorics.SimpleGraph.Staircase
import Mathlib.Tactic.Positivity

/-!
# The `Sym(3)` coboundary constant along Kozlov's staircase graphs

For a graph `G` on a finite linear order `V`, the transposition cochain `G.toCochain ht.mul_self`
with `t = Equiv.swap 0 1 : Perm (Fin 3)` has moved-point defect `2 * #G.oddTripleFinset`
(`SimpleGraph.defect_movedNorm_toCochain`). When `G` is cut-minimal,
`SimpleGraph.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq` gives
`gaugeDist = 2 * #G.edgeFinset`. Hence:

* `SimpleGraph.h1_complete_movedNorm_fin_three_le_of_isCutMinimal`: for a cut-minimal `G` with an
  edge,
  `h1 (complete V) (movedNorm (Fin 3)) ≤ #G.oddTripleFinset / #G.edgeFinset`.
* `h1_complete_movedNorm_fin_three_le_of_card_eq_mul`: applied to Kozlov's staircase graph
  `SimpleGraph.staircase q t` on `q (2 t + 1)` vertices, which is cut-minimal
  (`SimpleGraph.isCutMinimal_staircase`) with
  `3 * #oddTripleFinset = q (2 t + 1) * #edgeFinset`
  (`SimpleGraph.three_mul_card_oddTripleFinset_staircase`), this gives
  `h1 (complete V) (movedNorm (Fin 3)) ≤ card V / 3` whenever `card V = q (2 t + 1)`, `q, t ≥ 1`.

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Definition 3.2 and §3.1 (staircase graphs), Lemma 3.8 and Corollary 3.13 (cut-minimality),
  Lemma 3.10 (triangle count).
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792,
  Corollary 7 and Theorem 8 (the `Sym(3)` transfer).
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: this file adapts the staircase upper bound from `CoboundaryK3/Staircase.lean`,
  using `SimpleGraph.staircase` and `SimpleGraph.toCochain`.
-/

public section

namespace SimpleGraph

open Finset Equiv TauCeti TauCeti.TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- **Cut-minimal graphs bound the `Sym(3)` constant.** For a cut-minimal graph `G` on `V` with at
least one edge, `h1 (complete V) (movedNorm (Fin 3)) ≤ #G.oddTripleFinset / #G.edgeFinset`. -/
theorem h1_complete_movedNorm_fin_three_le_of_isCutMinimal (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsCutMinimal) (hE : 0 < #G.edgeFinset) :
    h1 (complete V) (Perm.movedNorm (Fin 3)) ≤
      (#G.oddTripleFinset : ℝ) / #G.edgeFinset := by
  have ht : (swap 0 1 : Perm (Fin 3)).IsSwap := Perm.swap_isSwap_iff.mpr (by decide)
  have hE' : (0 : ℝ) < 2 * #G.edgeFinset := by positivity
  have hgd : (G.toCochain ht.mul_self).gaugeDist (Perm.movedNorm (Fin 3)) = 2 * #G.edgeFinset :=
    (G.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq ht).mp hG
  refine (h1_le_div (hgd ▸ hE')).trans_eq ?_
  rw [G.defect_movedNorm_toCochain ht, hgd]
  exact mul_div_mul_left _ _ two_ne_zero

end SimpleGraph

namespace TauCeti

open Finset Equiv TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- **The staircase upper bound.** If `card V = q (2 t + 1)` with `q, t ≥ 1`, then
`h1 (complete V) (movedNorm (Fin 3)) ≤ card V / 3`, witnessed by Kozlov's staircase graph
`SimpleGraph.staircase q t`. -/
theorem h1_complete_movedNorm_fin_three_le_of_card_eq_mul {q t : ℕ} (hq : 0 < q) (ht : 0 < t)
    (hV : Fintype.card V = q * (2 * t + 1)) :
    h1 (complete V) (Perm.movedNorm (Fin 3)) ≤ (Fintype.card V : ℝ) / 3 := by
  let W := Fin (q * t) ⊕ Fin (q * t) ⊕ Fin q
  let _ : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  have hW : Fintype.card W = q * (2 * t + 1) := by
    simp only [W, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [h1_complete_eq_of_card_eq Perm.isConjInvariant_movedNorm (hV.trans hW.symm)]
  have hE2 := SimpleGraph.two_mul_card_edgeFinset_staircase q t
  have hO := SimpleGraph.three_mul_card_oddTripleFinset_staircase q t
  have hE : 0 < #(SimpleGraph.staircase q t).edgeFinset := by
    have : 0 < q ^ 2 * t * (t + 1) := by positivity
    omega
  refine (SimpleGraph.h1_complete_movedNorm_fin_three_le_of_isCutMinimal _
    (SimpleGraph.isCutMinimal_staircase q t) hE).trans_eq ?_
  have hE' : (0 : ℝ) < #(SimpleGraph.staircase q t).edgeFinset := by exact_mod_cast hE
  rw [hV, div_eq_div_iff hE'.ne' (by norm_num)]
  have h := congrArg (Nat.cast (R := ℝ)) hO
  push_cast at h ⊢
  -- the two odd-triple counts differ only in their `DecidableEq W` instances
  refine (mul_comm _ _).trans ?_
  convert h

end TauCeti
