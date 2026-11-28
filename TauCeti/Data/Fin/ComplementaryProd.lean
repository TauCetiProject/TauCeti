/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Nested products and sums over complementary `Fin` heights

Given two column-count profiles `c, c' : ℕ → ℕ` that are complementary on `1 ≤ h < N` in the sense
that `c' h = c (N - h)`, negation on `Fin N` pairs each positive height `h` with `N - h` while
fixing `0`. Consequently, a double product `∏ h : Fin N, ∏ j : Fin (c h), f h j` equals
`∏ h : Fin N, ∏ j : Fin (c' h), f' h j` whenever matching factors at complementary heights agree
and factors at height `0` are `1`, with the corresponding additive statement for sums.

## Main results

* `TauCeti.prod_fin_complementary_eq`: equality of nested products over complementary `Fin N`
  profiles.
* `TauCeti.sum_fin_complementary_eq`: the additive counterpart for nested sums.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/GLn/Dual.lean` (`New.GL.prod_columns_eq_prod_complementary`), equipped with
`@[to_additive]` for both multiplicative and additive commutative monoids.
-/

@[expose] public section

namespace TauCeti

/-- A nested product over `h : Fin N` and `j : Fin (c h)` equals the corresponding product for a
complementary profile `c'` satisfying `c' h = c (N - h)` on `1 ≤ h < N`, provided factors at
complementary heights `h + h' = N` with equal inner index agree and factors at height `0` are
`1`. -/
@[to_additive
  /-- A nested sum over `h : Fin N` and `j : Fin (c h)` equals the corresponding sum for a
  complementary profile `c'` satisfying `c' h = c (N - h)` on `1 ≤ h < N`, provided terms at
  complementary heights `h + h' = N` with equal inner index agree and terms at height `0` are
  `0`. -/]
theorem prod_fin_complementary_eq {M : Type*} [CommMonoid M] {N : ℕ} {c c' : ℕ → ℕ}
    (hc : ∀ h ∈ Finset.Ico 1 N, c' h = c (N - h))
    (f : ∀ h : Fin N, Fin (c h) → M) (f' : ∀ h : Fin N, Fin (c' h) → M)
    (h_match : ∀ (h h' : Fin N) (j : Fin (c h)) (j' : Fin (c' h')),
      (h : ℕ) + h' = N → (j : ℕ) = j' → f h j = f' h' j')
    (h_zero : ∀ (h : Fin N) (j : Fin (c h)), (h : ℕ) = 0 → f h j = 1)
    (h_zero' : ∀ (h : Fin N) (j : Fin (c' h)), (h : ℕ) = 0 → f' h j = 1) :
    ∏ h : Fin N, ∏ j : Fin (c h), f h j = ∏ h : Fin N, ∏ j : Fin (c' h), f' h j := by
  refine Finset.prod_equiv (Equiv.neg (Fin N)) (by simp) ?_
  rintro ⟨_ | h, hh⟩ -
  · simp [Fin.neg_def, h_zero, h_zero']
  · let h' : Fin N := -⟨h + 1, hh⟩
    have hneg : (h' : ℕ) = N - (h + 1) := by
      simp [h', Fin.neg_def, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.zero_lt_of_lt hh) (Nat.succ_pos h))]
    have hcard : c (h + 1) = c' h' := by
      rw [hneg, hc (N - (h + 1)) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
        Nat.sub_sub_self (Nat.le_of_lt hh)]
    exact Fintype.prod_equiv (finCongr hcard) _ _ fun j ↦
      h_match ⟨h + 1, hh⟩ h' j _ (by rw [hneg]; dsimp; omega) rfl

end TauCeti
