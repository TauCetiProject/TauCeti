/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Balanced replication of `Cochain.ofLt`

`Cochain.defect_ofLt_lex`: replacing each vertex of a finite linear order `V` by a cluster `ι`,
with value `1` inside clusters and a seed value between them, multiplies the defect of
`Cochain.ofLt` on the complete complex by `(Fintype.card ι) ^ 3`, for any group and any group norm.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792, Lemma 6.
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: the balanced replication of `CoboundaryK3/Replication.lean`.
-/

public section

open Finset Equiv

namespace TauCeti

open TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

namespace Cochain

variable {G : Type*} [Group G]

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

end TauCeti
