/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder

/-!
# Basic facts about monomial orders

* `MonomialOrder.toSyn_lt_toSyn_add`: a proper multiple of an exponent is larger in every monomial
  order.
-/

public section

open Finsupp

namespace MonomialOrder

variable {σ : Type*}

/-- A proper multiple of an exponent is larger in every monomial order. -/
theorem toSyn_lt_toSyn_add (m : MonomialOrder σ) (k : σ →₀ ℕ) {s : σ →₀ ℕ} (hs : s ≠ 0) :
    m.toSyn k < m.toSyn (k + s) :=
  m.toSyn_strictMono (lt_add_of_pos_right k (pos_iff_ne_zero.mpr hs))

end MonomialOrder
