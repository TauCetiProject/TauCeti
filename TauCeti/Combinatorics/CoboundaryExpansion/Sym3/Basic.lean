/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Basic
public import TauCeti.Combinatorics.SimpleGraph.OddTriangles
public import TauCeti.GroupTheory.Perm.MovedNorm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Defects of `Sym(3)`-valued cochains on the complete complex

Two triangle-defect counts for cochains `Cochain.ofLt (complete V) f` built from values on the
positively oriented pairs `u < v`:

* `Sym3.defect_ofLt_ite_adj`: for a graph `G` on `V`, the cochain that is the transposition
  `swap 0 1` on the edges of `G` and `1` elsewhere has moved-point defect twice the number of
  odd triangles of `G` (the triangles spanning one or three edges of `G`).
* `Cochain.defect_ofLt_lex`: balanced replication. Replacing each vertex of `V` by a cluster
  `ι`, with value `1` inside clusters and the seed value between them, on `V ×ₗ ι`, multiplies
  the defect by `(Fintype.card ι) ^ 3`, for any group and any group norm.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792, Lemma 6 and Corollary 7.
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: this file adapts the list-based counts of `CoboundaryK3/Basic.lean` and the
  balanced replication of `CoboundaryK3/Replication.lean`.
-/

public section

open Finset Equiv

namespace TauCeti

open TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

namespace Cochain

variable {G : Type*} [Group G]

/-- The holonomy of `Cochain.ofLt` around an increasing triple `u < v < w`. -/
theorem holonomy_ofLt_complete (f : V → V → G) {u v w : V} (huv : u < v) (hvw : v < w) :
    (ofLt (complete V) f).holonomy u v w = f u v * f v w * (f u w)⁻¹ := by
  have huw := huv.trans hvw
  rw [holonomy_def, ofLt_apply_of_lt _ ((adj_complete u v).mpr huv.ne) huv,
    ofLt_apply_of_lt _ ((adj_complete v w).mpr hvw.ne) hvw,
    ofLt_apply_of_gt _ ((adj_complete w u).mpr huw.ne') huw]

/-- **Balanced replication of the defect.** Replicating each vertex of `V` by a cluster `ι` (value
`1` inside clusters, the seed value `α i j` between clusters `i < j`) multiplies the defect by
`(Fintype.card ι) ^ 3`. -/
theorem defect_ofLt_lex {ι : Type*} [Fintype ι] [LinearOrder ι] (ℓ : GroupNorm G)
    (α : V → V → G) :
    (ofLt (complete (V ×ₗ ι)) fun x y =>
        if (ofLex x).1 = (ofLex y).1 then 1 else α (ofLex x).1 (ofLex y).1).defect ℓ =
      (Fintype.card ι : ℝ) ^ 3 * (ofLt (complete V) α).defect ℓ := by
  set f : V ×ₗ ι → V ×ₗ ι → G := fun x y =>
    if (ofLex x).1 = (ofLex y).1 then 1 else α (ofLex x).1 (ofLex y).1
  have hterm : ∀ (i j l : V) (a b c : ι),
      (if toLex (i, a) < toLex (j, b) ∧ toLex (j, b) < toLex (l, c) then
        ℓ ((ofLt (complete (V ×ₗ ι)) f).holonomy (toLex (i, a)) (toLex (j, b)) (toLex (l, c)))
        else 0) =
      if i < j ∧ j < l then ℓ ((ofLt (complete V) α).holonomy i j l) else 0 := by
    intro i j l a b c
    by_cases hlex : toLex (i, a) < toLex (j, b) ∧ toLex (j, b) < toLex (l, c)
    · rw [ite_eq_left hlex, holonomy_ofLt_complete _ hlex.1 hlex.2]
      have h1 := Prod.Lex.toLex_lt_toLex.mp hlex.1
      have h2 := Prod.Lex.toLex_lt_toLex.mp hlex.2
      simp only at h1 h2
      by_cases hijl : i < j ∧ j < l
      · rw [ite_eq_left hijl, holonomy_ofLt_complete _ hijl.1 hijl.2]
        simp [f, hijl.1.ne, hijl.2.ne, (hijl.1.trans hijl.2).ne]
      · rw [ite_eq_right hijl]
        rcases h1 with h1 | ⟨rfl, -⟩ <;> rcases h2 with h2 | ⟨rfl, -⟩
        · exact absurd ⟨h1, h2⟩ hijl
        · simp [f, h1.ne]
        · simp [f, h2.ne]
        · simp [f]
    · rw [ite_eq_right hlex]
      by_cases hijl : i < j ∧ j < l
      · exact absurd ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inl hijl.1),
          Prod.Lex.toLex_lt_toLex.mpr (Or.inl hijl.2)⟩ hlex
      · rw [ite_eq_right hijl]
  rw [defect_complete, defect_complete, sum_filter, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [← (toLex : V × ι ≃ V ×ₗ ι).sum_comp]
  simp only [← (toLex : V × ι ≃ V ×ₗ ι).sum_comp _, Fintype.sum_prod_type, hterm]
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  ring

end Cochain

namespace Sym3

/-- The holonomy of a triangle with `{1, swap 0 1}` labels moves `2` points exactly when an odd
number of its edges carry `swap 0 1`. -/
private theorem card_support_ite_mul_ite_mul_ite_inv (p r s : Prop) [Decidable p] [Decidable r]
    [Decidable s] :
    #((if p then swap 0 1 else 1 : Perm (Fin 3)) * (if r then swap 0 1 else 1) *
        (if s then swap 0 1 else 1)⁻¹).support = if Xor p (Xor s r) then 2 else 0 := by
  by_cases hp : p <;> by_cases hr : r <;> by_cases hs : s <;> simp [hp, hr, hs]

/-- **Defect of a graph cochain.** The cochain equal to `swap 0 1` on the edges of `G` and `1`
elsewhere has moved-point defect `2 * #G.oddTriangleFinset`. -/
theorem defect_ofLt_ite_adj (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Cochain.ofLt (complete V) fun u v => if G.Adj u v then swap 0 1 else 1).defect
        (Perm.movedNorm (Fin 3)) = 2 * #G.oddTriangleFinset := by
  rw [Cochain.defect_complete, sum_filter, SimpleGraph.card_oddTriangleFinset_eq_sum]
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
      card_support_ite_mul_ite_mul_ite_inv]
    by_cases hx : Xor (G.Adj u v) (Xor (G.Adj u w) (G.Adj v w)) <;> simp [h, hx]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]
    simp

end Sym3

end TauCeti
