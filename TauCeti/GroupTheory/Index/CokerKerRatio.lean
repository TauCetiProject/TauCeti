/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.Index

import Mathlib.Data.Rat.Cast.Defs

/-!
# Range index from rational cokernel-to-kernel ratios

When the rational cokernel-to-kernel ratio `[H : range f] / #ker f` of a group homomorphism
`f : G →* H` equals a nonzero natural number `t`, both the index `[H : range f]` and the kernel
order `#ker f` are nonzero (hence finite), and `[H : range f] = t * #ker f`.

## Main results

* `MonoidHom.index_range_eq_of_div_natCard_ker_eq` and
  `AddMonoidHom.index_range_eq_of_div_natCard_ker_eq`: if `(f.range.index : ℚ) / Nat.card f.ker = t`
  with `t ≠ 0`, then `f.range.index ≠ 0` and `f.range.index = t * Nat.card f.ker`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/ClassField/Global/ExistenceTheorem.lean` (`New.index_range_pow_eq`), generalized to
arbitrary group homomorphisms with an additive counterpart.
-/

@[expose] public section

/-- If the rational ratio `[H : range f] / #ker f` of a group homomorphism `f : G →* H` equals a
nonzero natural number `t`, then `range f` has finite index `t * #ker f` in `H`. -/
@[to_additive AddMonoidHom.index_range_eq_of_div_natCard_ker_eq
  /-- If the rational ratio `[H : range f] / #ker f` of an additive group homomorphism
  `f : G →+ H` equals a nonzero natural number `t`, then `range f` has finite index `t * #ker f` in
  `H`. -/]
theorem MonoidHom.index_range_eq_of_div_natCard_ker_eq {G H : Type*} [Group G] [Group H]
    (f : G →* H) {t : ℕ} (ht : t ≠ 0) (h : (f.range.index : ℚ) / Nat.card f.ker = t) :
    f.range.index ≠ 0 ∧ f.range.index = t * Nat.card f.ker := by
  have hne : (f.range.index : ℚ) / Nat.card f.ker ≠ 0 := by
    rw [h]
    exact Nat.cast_ne_zero.mpr ht
  obtain ⟨hidx, hker⟩ := div_ne_zero_iff.mp hne
  exact ⟨Nat.cast_ne_zero.mp hidx, by exact_mod_cast (div_eq_iff hker).mp h⟩
