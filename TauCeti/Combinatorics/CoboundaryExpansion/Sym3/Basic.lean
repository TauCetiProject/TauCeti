/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Basic
public import TauCeti.Combinatorics.SimpleGraph.OddTriangles
public import TauCeti.GroupTheory.Perm.MovedNorm
import Mathlib.Data.Fintype.Prod

/-!
# Defect of a graph cochain on the complete complex

For a graph `G` on a finite linear order `V`, the cochain `Cochain.ofLt (complete V)` that is the
transposition `swap 0 1` on the edges of `G` and `1` elsewhere has moved-point defect twice the
number of odd triangles of `G` (`SimpleGraph.defect_ofLt_ite_adj`).

The balanced-replication identity `Cochain.defect_ofLt_lex` is in
`TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Replication`.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792, Corollary 7.
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: this file adapts the list-based counts of `CoboundaryK3/Basic.lean`.
-/

public section

open Finset Equiv

namespace TauCeti

open TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

namespace Sym3

/-- The holonomy of a triangle with `{1, swap 0 1}` labels moves `2` points exactly when an odd
number of its edges carry `swap 0 1`. -/
private theorem card_support_ite_mul_ite_mul_ite_inv (p r s : Prop) [Decidable p] [Decidable r]
    [Decidable s] :
    #((if p then swap 0 1 else 1 : Perm (Fin 3)) * (if r then swap 0 1 else 1) *
        (if s then swap 0 1 else 1)⁻¹).support = if Xor p (Xor s r) then 2 else 0 := by
  by_cases hp : p <;> by_cases hr : r <;> by_cases hs : s <;> simp [hp, hr, hs]

end Sym3

end TauCeti

namespace SimpleGraph

open Finset Equiv TauCeti TauCeti.TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- **Defect of a graph cochain.** The cochain equal to `swap 0 1` on the edges of `G` and `1`
elsewhere has moved-point defect `2 * #G.oddTriangleFinset`. -/
theorem defect_ofLt_ite_adj (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Cochain.ofLt (complete V) fun u v => if G.Adj u v then swap 0 1 else 1).defect
        (Perm.movedNorm (Fin 3)) = 2 * #G.oddTriangleFinset := by
  rw [Cochain.defect_complete, sum_filter, card_oddTriangleFinset_eq_sum]
  simp only [Fintype.sum_prod_type]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun w _ => ?_
  by_cases h : u < v ∧ v < w
  · rw [ite_eq_left h, Cochain.holonomy_ofLt_complete _ h.1 h.2, Perm.movedNorm_apply,
      TauCeti.Sym3.card_support_ite_mul_ite_mul_ite_inv]
    by_cases hx : Xor (G.Adj u v) (Xor (G.Adj u w) (G.Adj v w)) <;> simp [h, hx]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]
    simp

end SimpleGraph
