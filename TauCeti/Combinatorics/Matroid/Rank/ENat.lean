/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Natural-number truncations of the rank function

This file bounds the natural number `(M.eRk X).toNat`, which serves as the rank of `X` in
rank-generating invariants of finite matroids such as the Tutte polynomial.

## Main declarations

* `Matroid.toNat_eRk_le_card`: the rank of a finite set is at most its cardinality.
* `Matroid.toNat_eRk_le_toNat_eRank`: in a matroid of finite rank, the rank of a set is at most
  the rank of the matroid.
-/

public section

namespace Matroid

variable {α : Type*} (M : Matroid α)

/-- The rank of a finite set is at most its cardinality. -/
lemma toNat_eRk_le_card (A : Finset α) : (M.eRk A).toNat ≤ A.card := by
  have h := M.eRk_le_encard A
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  simpa using ENat.toNat_le_toNat h (ENat.natCast_ne_top _)

/-- In a matroid of finite rank, the rank of a set is at most the rank of the matroid. -/
lemma toNat_eRk_le_toNat_eRank [M.RankFinite] (X : Set α) : (M.eRk X).toNat ≤ M.eRank.toNat :=
  ENat.toNat_le_toNat (M.eRk_le_eRank X) (M.eRank_ne_top_iff.2 inferInstance)

end Matroid
