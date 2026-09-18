/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder

/-!
# Generators of a domain algebra of prime dimension

A domain that is an algebra of prime dimension over a field has no subalgebras other than the
field itself and the whole algebra (`Subalgebra.isSimpleOrder_of_finrank_prime`), so every
element outside the base field generates the algebra.

## Main results

* `TauCeti.Algebra.adjoin_singleton_eq_top_of_finrank_prime`: in a domain algebra of prime
  dimension over a field, `Algebra.adjoin F {x} = ⊤` for every `x` outside the base field.
-/

public section

/-- In a domain algebra of prime dimension over a field, every element outside the base field
generates the algebra. -/
theorem TauCeti.Algebra.adjoin_singleton_eq_top_of_finrank_prime {F A : Type*} [Field F] [Ring A]
    [IsDomain A] [Algebra F A] (hp : Nat.Prime (Module.finrank F A)) {x : A}
    (hx : x ∉ (⊥ : Subalgebra F A)) : Algebra.adjoin F {x} = ⊤ :=
  ((Subalgebra.isSimpleOrder_of_finrank_prime F A hp).eq_bot_or_eq_top (Algebra.adjoin F {x}))
    |>.resolve_left fun h => hx (h ▸ Algebra.subset_adjoin (Set.mem_singleton x))
