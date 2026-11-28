/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Cardinality factorizations for additive group homomorphisms

This file provides two `Nat.card` factorization identities for additive group homomorphisms
and the multiplicative cancellation step used to pass from cocycle counts to cohomology-class
counts in Greenberg–Wiles inequalities.

## Main results

* `TauCeti.card_eq_card_ker_mul_card_mul_card_range`: given `r : T →+ J` and `p : r.ker →+ D`
  with `p.range = ⊤`, `Nat.card T = Nat.card p.ker * Nat.card D * Nat.card r.range`.
* `TauCeti.card_pow_succ_eq_card_mul_card_range_mul_card_ker`: given `d : A →+ B` and a
  surjection `j : (ι → A) × d.ker →+ H`,
  `Nat.card A ^ (Fintype.card ι + 1) = Nat.card H * Nat.card d.range * Nat.card j.ker`.
* `TauCeti.mul_pow_le_of_mul_eq`: the arithmetic cancellation turning a cocycle bound
  `c * b * m ^ (S.card + f) ≤ Y * ∏ v ∈ S, l v * bv v` into
  `c * m ^ (f + 1) * ∏ v ∈ S, hv v ≤ Y * h * ∏ v ∈ S, l v`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean (commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`), files
  `src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean` (declarations
  `AddMonoidHom.card_eq_card_ker_mul_card_mul_card_range`,
  `AddMonoidHom.card_pow_succ_eq_card_mul_card_range_mul_card_ker`) and
  `src/Lib/ClassField/GreenbergWiles/SelmerClasses.lean` (declaration
  `New.selmerH1.mul_pow_le_of_le`); Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti

/-- Counting along `r : T →+ J` and a surjection `p : r.ker →+ D` (`p.range = ⊤`):
`Nat.card T = Nat.card p.ker * Nat.card D * Nat.card r.range`. -/
theorem card_eq_card_ker_mul_card_mul_card_range {T J D : Type*} [AddCommGroup T]
    [AddCommGroup J] [AddCommGroup D] (r : T →+ J) (p : r.ker →+ D) (hp : p.range = ⊤) :
    Nat.card T = Nat.card p.ker * Nat.card D * Nat.card r.range := by
  rw [← r.ker.card_mul_index, ← p.ker.card_mul_index, AddSubgroup.index_ker,
    AddSubgroup.index_ker, hp, AddSubgroup.card_top]

/-- Counting along `d : A →+ B` and a surjection `j : (ι → A) × d.ker →+ H`:
`Nat.card A ^ (Fintype.card ι + 1) = Nat.card H * Nat.card d.range * Nat.card j.ker`. -/
theorem card_pow_succ_eq_card_mul_card_range_mul_card_ker {ι A B H : Type*} [Fintype ι]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup H] (d : A →+ B) (j : (ι → A) × d.ker →+ H)
    (hj : Function.Surjective j) :
    Nat.card A ^ (Fintype.card ι + 1) = Nat.card H * Nat.card d.range * Nat.card j.ker := by
  rw [pow_succ, ← Nat.card_eq_fintype_card, ← Nat.card_fun, ← d.ker.card_mul_index, ← mul_assoc,
    ← Nat.card_prod, ← j.ker.card_mul_index, AddSubgroup.index_ker, AddSubgroup.index_ker,
    j.range_eq_top.mpr hj, AddSubgroup.card_top, mul_rotate]

/-- The arithmetic cancellation that turns a cocycle-level Greenberg–Wiles bound into a class-level
bound. Given `b * h = m`, `bv v * hv v = m` for `v ∈ S`, and `0 < m`, if
`c * b * m ^ (S.card + f) ≤ Y * ∏ v ∈ S, l v * bv v`, then
`c * m ^ (f + 1) * ∏ v ∈ S, hv v ≤ Y * h * ∏ v ∈ S, l v`. -/
theorem mul_pow_le_of_mul_eq {ι : Type*} (S : Finset ι) {c b h m f Y : ℕ} {l bv hv : ι → ℕ}
    (hb : b * h = m) (hbv : ∀ v ∈ S, bv v * hv v = m) (hm : 0 < m)
    (h_le : c * b * m ^ (S.card + f) ≤ Y * ∏ v ∈ S, l v * bv v) :
    c * m ^ (f + 1) * ∏ v ∈ S, hv v ≤ Y * h * ∏ v ∈ S, l v := by
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hm S.card)
  calc c * m ^ (f + 1) * (∏ v ∈ S, hv v) * m ^ S.card
      = c * b * m ^ (S.card + f) * (h * ∏ v ∈ S, hv v) := by
        rw [show c * b * m ^ (S.card + f) * (h * ∏ v ∈ S, hv v) =
          c * (b * h) * m ^ (S.card + f) * ∏ v ∈ S, hv v by ring, hb]
        ring
    _ ≤ Y * (∏ v ∈ S, l v * bv v) * (h * ∏ v ∈ S, hv v) := by gcongr
    _ = Y * h * (∏ v ∈ S, l v) * ∏ v ∈ S, bv v * hv v := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring
    _ = Y * h * (∏ v ∈ S, l v) * m ^ S.card := by rw [Finset.prod_congr rfl hbv, Finset.prod_const]

end TauCeti
