/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.FieldTheory.Finite.FrobeniusFixed

import TauCeti.FieldTheory.IsSepClosed

/-!
# Splitting criterion over a finite field in a separably closed extension

Since a finite field `k` is perfect, every polynomial `p : k[X]` splits in any separably closed
extension field `K` (`IsSepClosed.splits_codomain_of_perfectField`). Combining this with
`TauCeti.FiniteField.splits_of_forall_aeval_eq_zero_pow_natCard_eq` shows that `p` splits over
`k` as soon as every root `x : K` of `p` satisfies `x ^ |k| = x`.

## Main results

* `TauCeti.FiniteField.splits_of_isSepClosed_of_forall_aeval_eq_zero_pow_natCard_eq`: a polynomial
  over a finite field `k` splits over `k` if every root in a separably closed extension `K`
  satisfies `x ^ |k| = x`.

## Provenance

Adapted from grh-lean
(https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/LocalGL/Green/LabelCharacters.lean` (`New.splits_of_forall_root_pow_card_eq`).
-/

public section

open Polynomial

namespace TauCeti.FiniteField

/-- A polynomial `p : k[X]` over a finite field `k` splits over `k` if every root of `p` in a
separably closed extension field `K` satisfies `x ^ |k| = x`. -/
theorem splits_of_isSepClosed_of_forall_aeval_eq_zero_pow_natCard_eq {k K : Type*} [Field k]
    [Finite k] [Field K] [Algebra k K] [IsSepClosed K] {p : k[X]}
    (h_roots : ∀ x : K, aeval x p = 0 → x ^ Nat.card k = x) : p.Splits :=
  splits_of_forall_aeval_eq_zero_pow_natCard_eq
    (IsSepClosed.splits_codomain_of_perfectField p) h_roots

end TauCeti.FiniteField
