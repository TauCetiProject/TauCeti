/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Two-entry tuples with normalized, mutually dividing first entries

Arithmetic of `Fin 2 → α` over a cancellative normalization monoid `α`. Nothing here involves
matrices; the results are stated for tuples so that callers holding a diagonal, a pair of
invariant factors, or any other two elements can use them without dragging in linear algebra.
Over `ℤ`, where `normalize z = z` exactly when `0 ≤ z` (`Int.normalize_of_nonneg`), the
normalization hypotheses are sign conditions.

## Main results

* `TauCeti.fin_two_eq_of_normalize_eq_of_dvd_of_dvd_of_mul_eq_mul`: two tuples with normalized,
  mutually dividing first entries, the first of them nonzero, and equal products are equal.

## Provenance

Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck), Apache-2.0, at
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, from
`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`. The source's
`snf_mutual_dvd_eq` draws the same conclusion over `ℤ` from Smith-normal-form data and routes
through `smith_normal_form_unique`; `fin_two_eq_of_normalize_eq_of_dvd_of_dvd_of_mul_eq_mul` keeps
none of those matrix hypotheses and does not use it.
-/

public section

namespace TauCeti

variable {α : Type*} [MonoidWithZero α] [NormalizationMonoid α] [IsLeftCancelMulZero α]

/-- **Two `Fin 2 → α` tuples with normalized, mutually dividing first entries and equal products
are equal**, provided the first entries are nonzero. The first entries agree by
`dvd_antisymm_of_normalize_eq`, and the second is then pinned by cancelling the first out of the
product.

Only the *first* entries are constrained; the second ones are arbitrary. Over `ℤ` the hypotheses
on the first entries say that `a 0` is positive and `b 0` nonnegative. -/
theorem fin_two_eq_of_normalize_eq_of_dvd_of_dvd_of_mul_eq_mul {a b : Fin 2 → α}
    (ha : normalize (a 0) = a 0) (hb : normalize (b 0) = b 0) (ha0 : a 0 ≠ 0)
    (hab : a 0 ∣ b 0) (hba : b 0 ∣ a 0) (hprod : a 0 * a 1 = b 0 * b 1) : a = b := by
  have h0 : a 0 = b 0 := dvd_antisymm_of_normalize_eq ha hb hab hba
  exact funext <| Fin.forall_fin_two.2 ⟨h0, mul_left_cancel₀ ha0 (by rw [hprod, h0])⟩

end TauCeti

end
