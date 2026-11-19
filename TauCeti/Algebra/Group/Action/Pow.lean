/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Data.Nat.Find

/-!
# Powers of an element acting on strings and on translated families

For a monoid `M` acting on a type `V` with a zero, an element `x : M` and a vector `w : V`, the
`x`-string of `w` is the sequence `w, x • w, x² • w, …`. This file shows that if the string
contains `0` and `w ≠ 0`, then some nonzero term `xⁿ • w` is immediately followed by the zero
term `x • xⁿ • w`. The action need not fix `0`, so later terms of the string may be nonzero
again. Raising and lowering operators of representations, such as `E` and `F` for `U_q(sl₂)`,
use this to produce highest- and lowest-weight vectors. When the action fixes the zero, once a
term of the string vanishes all later terms vanish.

An element `g` that translates a family `c : A → α`, indexed by an additive monoid, by `t`, in
the sense that `g • c n = c (n + t)` for all `n`, translates it by `k • t` under its power `gᵏ`;
for a group acting and an additive group of indices this holds for integer powers as well. An
automorphism of a tree acting on its axis, parametrized by the integers, is an example.

## Main results

* `TauCeti.exists_pow_smul_ne_zero_and_smul_eq_zero`: if `xⁿ • w = 0` for some `n` and `w ≠ 0`,
  then `xⁿ • w ≠ 0` and `x • xⁿ • w = 0` for some `n`.
* `TauCeti.pow_smul_eq_zero_of_le`: for an action fixing `0`, if `xᵐ • w = 0` and `m ≤ n`, then
  `xⁿ • w = 0`.
* `TauCeti.pow_smul_eq_add_nsmul`, `TauCeti.zpow_smul_eq_add_zsmul`: if `g • c n = c (n + t)` for
  all `n`, then `gᵏ • c n = c (n + k • t)`.
-/

public section

namespace TauCeti

variable {M V : Type*} [Monoid M] [MulAction M V] [Zero V]

/-- If some power of `x` kills a nonzero vector `w`, then the string `w, x • w, x² • w, …` has a
nonzero term `xⁿ • w` immediately followed by the zero term `x • xⁿ • w`. -/
theorem exists_pow_smul_ne_zero_and_smul_eq_zero {x : M} {w : V} (hw0 : w ≠ 0)
    (h : ∃ n : ℕ, x ^ n • w = 0) : ∃ n : ℕ, x ^ n • w ≠ 0 ∧ x • x ^ n • w = 0 := by
  classical
  have hn : 0 < Nat.find h :=
    Nat.pos_of_ne_zero fun hn ↦ hw0 (by simpa [hn] using Nat.find_spec h)
  refine ⟨Nat.find h - 1, Nat.find_min h (by omega), ?_⟩
  rw [← mul_smul, ← pow_succ', Nat.sub_add_cancel hn]
  exact Nat.find_spec h

/-- If a power of `x` kills `w` and scalars fix `0`, then every higher power of `x` kills `w`.
This is the action counterpart of `pow_mul_eq_zero_of_le`. It only uses `x • 0 = 0` and
`(x * y) • w = x • y • w` (`IsScalarTower M M N`); no addition on `N` is needed. -/
theorem pow_smul_eq_zero_of_le {M N : Type*} [Monoid M] [Zero N] [SMulZeroClass M N]
    [IsScalarTower M M N] {x : M} {w : N} {m n : ℕ} (hmn : m ≤ n) (h : x ^ m • w = 0) :
    x ^ n • w = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, ← smul_eq_mul, smul_assoc, h, smul_zero]

section Translate

variable {α A : Type*}

/-- If `g` translates a family `c` indexed by an additive monoid by `t`, then `gᵏ` translates it
by `k • t`. -/
theorem pow_smul_eq_add_nsmul {M : Type*} [Monoid M] [MulAction M α] [AddMonoid A] {g : M}
    {c : A → α} {t : A} (hg : ∀ n, g • c n = c (n + t)) (k : ℕ) (n : A) :
    g ^ k • c n = c (n + k • t) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, ih, hg, succ_nsmul, add_assoc]

/-- If `g` translates a family `c` indexed by an additive group by `t`, then `gᵏ` translates it by
`k • t` for every integer `k`. -/
theorem zpow_smul_eq_add_zsmul {G : Type*} [Group G] [MulAction G α] [AddGroup A] {g : G}
    {c : A → α} {t : A} (hg : ∀ n, g • c n = c (n + t)) (k : ℤ) (n : A) :
    g ^ k • c n = c (n + k • t) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast, natCast_zsmul, pow_smul_eq_add_nsmul hg]
  · rw [zpow_neg, zpow_natCast, inv_smul_eq_iff, pow_smul_eq_add_nsmul hg, neg_zsmul,
      natCast_zsmul, neg_add_cancel_right]

end Translate

end TauCeti
